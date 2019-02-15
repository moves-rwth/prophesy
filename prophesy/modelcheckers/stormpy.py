import logging
import time
import os
import subprocess

from prophesy.config import modules
from prophesy.exceptions.module_error import ModuleError
from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.modelcheckers.pmc import BisimulationType
from prophesy.exceptions.configuration_error import ConfigurationError
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError
from prophesy.input.solutionfunctionfile import ParametricResult
from prophesy.data.constant import Constants
from prophesy.data.samples import InstantiationResultDict
from prophesy.regions.region_checker import RegionCheckResult
from prophesy.regions.welldefinedness import WelldefinednessResult
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.data.model_type import ModelType
import prophesy.adapter.stormpy as stormpy
import prophesy.adapter.pycarl as pc

logger = logging.getLogger(__name__)


class StormpyModelChecker(ParametricProbabilisticModelChecker):
    """
    Class wrapping the stormpy bindings.
    """

    def __init__(self):
        """
        Initialize and check if stormpy is available.
        """
        if not modules.is_module_available("stormpy"):
            raise ModuleError(
                "Module stormpy is needed for using the Python API for Storm. Maybe your config is outdated?")

        self.drnfile = None
        self.prismfile = None
        self.pctlformula = None
        self.constants = None
        self.bisimulation = stormpy.BisimulationType.STRONG
        self.simplification = True
        self._model_building_time = None
        self._instantiated_model_checking_time = 0.0
        self._samples_checked = 0
        self._welldefined_checker = None
        self._states_before_bisim = None
        self._transitions_before_bisim = None
        # Storing objects of stormpy for incremental calls
        self._program = None
        self._model = None
        self._parameter_constraints = None
        self._parameter_mapping_inverse = None
        self._graph_preservation_constraints = None
        self._parameter_mapping = None
        self._model_instantiator = None
        self._instantiation_checker = None
        self._pla_checker = None
        self._pla_threshold = None
        self._pla_checker_time = 0.0
        self._regions_checked = 0
        self._environment = stormpy.Environment()

    def name(self):
        return "stormpy"

    def version(self):
        return str(stormpy.info.Version.short)

    @property
    def model_building_time(self):
        return self._model_building_time

    @property
    def nr_samples_checked(self):
        return self._samples_checked

    @property
    def instantiated_model_checking_time(self):
        return self._instantiated_model_checking_time

    @property
    def region_model_checking_time(self):
        return self._pla_checker_time

    @property
    def nr_regions_checked(self):
        return self._regions_checked

    def set_pctl_formula(self, formula):
        if self._program is None:
            logger.debug("Parse formula {} without a program.".format(formula))
            self.pctlformula = stormpy.parse_properties(str(formula))
        else:
            logger.debug("Load formula {} with respect to program.".format(formula))
            self.pctlformula = stormpy.parse_properties_for_prism_program(str(formula), self._program)
        # Reset formula for PLA
        self._pla_threshold = None

    def _reset_internal(self):
        self.drnfile = None
        self.prismfile = None
        self.constants = None
        self._program = None
        self._model = None
        self._parameter_constraints = None
        self._graph_preservation_constraints = None
        self._parameter_mapping = None
        self._parameter_mapping_inverse = None
        self._model_instantiator = None
        self._pla_checker = None
        self._welldefined_checker = None
        self._states_before_bisim = None
        self._transitions_before_bisim = None
        self._instantiation_checker = None
        self._transform_from_continuous = False

    @property
    def nr_states_before_bisim(self):
        self.get_model()
        return self._states_before_bisim

    @property
    def nr_transitions_before_bisim(self):
        self.get_model()
        return self._transitions_before_bisim

    @property
    def nr_states(self):
        self.get_model()
        return self._model.nr_states

    @property
    def nr_transitions(self):
        self.get_model()
        return self._model.nr_transitions

    def usage_stats(self):
        return "Checked {} samples in {} s\nChecked {} regions in {} s\n".format(self.nr_samples_checked,self.instantiated_model_checking_time, self.nr_regions_checked, self.region_model_checking_time)

    def set_welldefined_checker(self, checker):
        self._welldefined_checker = checker

    def load_model_from_drn(self, drnfile, constants=Constants()):
        self._reset_internal()
        self.drnfile = drnfile
        self.constants = constants
        self._transform_from_continuous = drnfile.do_transform and drnfile.model_type.is_continuous_time()

    def load_model_from_prismfile(self, prism_file, constants=Constants()):
        logger.debug("Load model from prism file")
        self._reset_internal()
        self.prismfile = prism_file
        self.constants = constants
        prismcompatibility = True if self.prismfile.model_type == ModelType.CTMC else False
        self._program = stormpy.parse_prism_program(self.prismfile.location, prismcompatibility)
        self._transform_from_continuous = prism_file.do_transform and prism_file.model_type.is_continuous_time()

        if not self._program.undefined_constants_are_graph_preserving:
            # Need to instantiate constants
            description = stormpy.SymbolicModelDescription(self._program)
            constants_string = self.constants.to_key_value_string(to_float=False) if self.constants else ""
            constant_definitions = description.parse_constant_definitions(constants_string)
            self._program = description.instantiate_constants(constant_definitions)

            if description.is_prism_program:
                self._program = self._program.as_prism_program()
            elif description.is_jani_model:
                self._program = self._program.as_jani_model()
            else:
                raise RuntimeError("Symbolic description type not known")

    def set_bisimulation_type(self, bisimulation_type):
        if bisimulation_type == BisimulationType.weak:
            self.bisimulation = stormpy.BisimulationType.WEAK
        elif bisimulation_type == BisimulationType.strong:
            self.bisimulation = stormpy.BisimulationType.STRONG
        elif bisimulation_type == BisimulationType.none:
            self.bisimulation = None
        else:
            raise ConfigurationError("Bisimulation type {} not valid.".format(bisimulation_type))

    def display_model(self):
        logger.debug("Display model")
        model = self.get_model()
        dotstring = model.to_dot()
        # TODO make graphviz optional.
        import pygraphviz as pgv
        from prophesy.config import configuration
        logger.debug("rendering...")
        G = pgv.AGraph(dotstring)
        G.layout()
        location = os.path.join(configuration.get_plots_dir(),"model.ps")
        G.draw(location)
        subprocess.call(["open", location])

    def has_built_model(self):
        return self._model is not None

    def get_model(self):
        """
        Get model.
        If model is not built before, first build the model and (optionally) perform bisimulation.
        :return: Model.
        """
        if self._model is None:
            logger.info("Build model")

            if self.prismfile is None and self.drnfile is None:
                raise NotEnoughInformationError("Model description not set.")
            if self.pctlformula is None:
                raise NotEnoughInformationError("PCTL formula not set.")

            start_time = time.time()
            if self.prismfile:
                if not self._program.undefined_constants_are_graph_preserving:
                    raise RuntimeError("Given model file still contains undefined constants")

                if self.prismfile.nr_parameters() == 0:
                    assert not self._program.has_undefined_constants
                    self._model = stormpy.build_model(self._program, self.pctlformula)
                else:
                    assert self._program.has_undefined_constants
                    self._model = stormpy.build_parametric_model(self._program, self.pctlformula)
            elif self.drnfile:
                self._model = stormpy.build_parametric_model_from_drn(self.drnfile.location)

            self._states_before_bisim = self._model.nr_states
            self._transitions_before_bisim = self._model.nr_transitions
            logger.debug("Built a model with {} states and {} transitions".format(self._states_before_bisim, self._transitions_before_bisim))

            if self._transform_from_continuous:
                logger.info("Transform to discrete time model")
                self._model, raw_transformed = stormpy.transform_to_discrete_time_model(self._model, self.pctlformula)
                self.pctlformula = [stormpy.Property("transformed", raw_transformed[0], comment="transformed of {}".format(
                    str(self.pctlformula[0].raw_formula)))]

            self._model.reduce_to_state_based_rewards()
            if self.bisimulation == stormpy.BisimulationType.STRONG or self.bisimulation == stormpy.BisimulationType.WEAK:
                logger.info("Perform bisimulation")
                self._model = stormpy.perform_bisimulation(self._model, self.pctlformula, self.bisimulation)

            if self.simplification:
                if self._model.model_type in [stormpy.storage.ModelType.CTMC, stormpy.storage.ModelType.MA]:
                    logger.warning("Simplification is not supported for CTMCs/MAs.")
                else:
                    if self.pctlformula is None:
                        raise NotEnoughInformationError("Simplification can only be exectued w.r.t. a single, set formula")

                    self._model, raw_simplified = stormpy.pars.simplify_model(self._model, self.pctlformula[0].raw_formula)
                    self.pctlformula = [stormpy.Property("simplified", raw_simplified, comment="simplified of {}".format(str(self.pctlformula[0].raw_formula)))]

            self._model_building_time = time.time() - start_time

        return self._model

    def get_parameter_mapping(self, prophesy_parameters, from_storm = False):
        """Get a mapping from prophesy parameters to model parameters in stormpy (or the other way around)."""

        def get_matching_model_parameter(model_parameters, variable_name):
            """Return matching parameter or None."""
            return next((v for v in model_parameters if v.name == variable_name), None)

        if self._parameter_mapping_inverse is None and from_storm:
            self._parameter_mapping_inverse = {}
            model_parameters = self.get_model().collect_probability_parameters() | self.get_model().collect_reward_parameters()
            for parameter in prophesy_parameters:
                model_param = get_matching_model_parameter(model_parameters, parameter.name)
                # assert model_param is not None
                self._parameter_mapping_inverse[model_param] = parameter


        if self._parameter_mapping is None and not from_storm:
            self._parameter_mapping = {}
            model_parameters = self.get_model().collect_probability_parameters() | self.get_model().collect_reward_parameters()
            for parameter in prophesy_parameters:
                model_param = get_matching_model_parameter(model_parameters, parameter.name)
                #assert model_param is not None
                self._parameter_mapping[parameter] = model_param

            for parameter in prophesy_parameters:
                assert parameter in self._parameter_mapping, repr(parameter) + " not in  " + str(self._parameter_mapping)

        if from_storm:
            return self._parameter_mapping_inverse
        return self._parameter_mapping

    def get_parameter_constraints(self):
        if self._parameter_constraints is None or self._graph_preservation_constraints is None:
            # Collect constraints if not already there
            logger.info("Call stormpy for constraints")

            collector = stormpy.ConstraintCollector(self.get_model())
            self._parameter_constraints = []
            self._graph_preservation_constraints = []
            # Convert formulas to standard type (CLN, GMP)
            for formula in collector.wellformed_constraints:
                converted_formula = pc.convert_from_storm_type(formula)
                self._parameter_constraints.append(converted_formula)
            for formula in collector.graph_preserving_constraints:
                converted_formula = pc.convert_from_storm_type(formula)
                self._graph_preservation_constraints.append(converted_formula)
            logger.info("Stormpy finished collecting constraints")

        return self._parameter_constraints, self._graph_preservation_constraints

    def get_model_instantiator(self):
        """
        Return model instantiator.
        :return: Model instantiator.
        """
        if self._model_instantiator is None:

            if self.get_model().model_type == stormpy.storage.ModelType.DTMC:
                self._model_instantiator = stormpy.pars.PDtmcInstantiator(self.get_model())
            elif self.get_model().model_type == stormpy.storage.ModelType.MDP:
                self._model_instantiator = stormpy.pars.PMdpInstantiator(self.get_model())
            elif self.get_model().model_type == stormpy.storage.ModelType.CTMC:
                self._model_instantiator = stormpy.pars.PCtmcInstantiator(self.get_model())
            elif self.get_model().model_type == stormpy.storage.ModelType.MA:
                self._model_instantiator = stormpy.pars.PMaInstantiator(self.get_model())
            else:
                return NotImplementedError("Model instantiator for {} is not supported.".format(self.get_model().model_type))
        return self._model_instantiator

    def get_model_instantiation_checker(self):
        only_initial_states = True
        if self._instantiation_checker is None:
            logger.debug("Create instantiation checker...")
            if self.get_model().model_type == stormpy.storage.ModelType.DTMC:
                self._instantiation_checker = stormpy.pars.PDtmcInstantiationChecker(self.get_model())
            elif self.get_model().model_type == stormpy.storage.ModelType.MDP:
                self._instantiation_checker = stormpy.pars.PMdpInstantiationChecker(self.get_model())
            else:
                raise NotImplementedError("Model instantiator for {} is not supported.".format(self.get_model().model_type))
            self._instantiation_checker.specify_formula(stormpy.ParametricCheckTask(self.pctlformula[0].raw_formula, only_initial_states))
            self._instantiation_checker.set_graph_preserving(True)
            logger.debug("...done.")

        return self._instantiation_checker



    def get_pla_checker(self, threshold, splitting_assistance = False, allow_simplifications=True):
        """
        Return model checker for PLA.
        :param threshold: Threshold in formula.
        :param splitting_assistance: Should splitting assistance be turned on (induces a mild performance penalty)
        :param allow_simplifications: Allow model simplifications in the checker (prevents using solutions for all states, induces an overhead on simplified models)
        :return: PLA model checker.
        """
        if self._pla_checker is None or self._pla_threshold != threshold:
            logger.debug("Generate new PLA Checker")
            #TODO what should we do if there is a PLA checker with the wrong settings.
            self._pla_threshold = threshold
            # Set formula for PLA
            formula = self.pctlformula[0].raw_formula
            if threshold is not None:
                expression_manager = stormpy.ExpressionManager()
                expression = expression_manager.create_rational(pc.convert_from_storm_type(threshold))
                formula.set_bound(stormpy.logic.ComparisonType.LESS, expression)
            # Create PLA checker
            if self.get_model().model_type == stormpy.storage.ModelType.DTMC:
                self._pla_checker = stormpy.pars.DtmcParameterLiftingModelChecker()
            elif self.get_model().model_type == stormpy.storage.ModelType.MDP:
                self._pla_checker = stormpy.pars.MdpParameterLiftingModelChecker()
            else:
                # TODO implement transformation for MA/CTMC (Probably already somewhere else?)
                return NotImplementedError("We have not implemented model transformation to DTMCs/MDPs yet")
            self._pla_checker.specify(self._environment, self.get_model(), formula, splitting_assistance, allow_simplifications)
        return self._pla_checker

    def get_rational_function(self):
        self.get_model()
        # Compute rational function
        logger.info("Compute solution function")
        result = stormpy.model_checking(self._model, self.pctlformula[0]).at(self._model.initial_states[0])
        rational_function = pc.convert_from_storm_type(result)
        logger.info("Stormpy model checking finished successfully")

        # Collect constraints
        parameter_constraints, graph_preservation_constraints = self.get_parameter_constraints()

        return ParametricResult(self.prismfile.parameters if self.prismfile else self.drnfile.parameters, parameter_constraints, graph_preservation_constraints, rational_function)

    def _check_welldefined(self, samplepoint):
        return self._welldefined_checker.check(samplepoint) == WelldefinednessResult.Welldefined

    def perform_sampling(self, sample_points, surely_welldefined=False):
        if not surely_welldefined:
            logger.warning("Sampling assumes (without any checks) that the point is welldefined")
        # Perform sampling with model instantiator
        logger.info("Call stormpy for sampling")
        parameter_mapping = self.get_parameter_mapping(sample_points[0].get_parameters())
        samples = InstantiationResultDict({p: self.sample_single_point(p, parameter_mapping) for p in sample_points})
        logger.info("Sampling with stormpy successfully finished")
        return samples

    def sample_single_point(self, parameter_instantiation, parameter_mapping):
        # Instantiate point and check result
        #model_instantiator = self.get_model_instantiator()
        model_instatiation_checker = self.get_model_instantiation_checker()
        point = {parameter_mapping[parameter]: pc.convert_to_storm_type(val) for parameter, val in
                 parameter_instantiation.items() if parameter_mapping[parameter] is not None}
        start = time.time()
        #instantiated_model = model_instantiator.instantiate(point)
        result = pc.convert_from_storm_type(model_instatiation_checker.check(self._environment,point).at(self.get_model().initial_states[0]))
        #result = pc.convert_from_storm_type(
        #    stormpy.model_checking(instantiated_model, self.pctlformula[0]).at(instantiated_model.initial_states[0]))
        self._instantiated_model_checking_time += time.time() - start
        self._samples_checked += 1
        return result

    def mc_single_point(self, parameter_instantiation, parameter_mapping=None):
        if parameter_mapping is None:
            parameter_mapping = self.get_parameter_mapping(parameter_instantiation.get_parameters())
        model_instantiator = self.get_model_instantiator()
        point = {parameter_mapping[parameter]: pc.convert_to_storm_type(val) for parameter, val in
                 parameter_instantiation.items() if parameter_mapping[parameter] is not None}
        start = time.time()
        instantiated_model = model_instantiator.instantiate(point)
        result = stormpy.model_checking(instantiated_model, self.pctlformula[0])
        self._instantiated_model_checking_time += time.time() - start
        self._samples_checked += 1
        return result


    def check_hyperrectangle(self, parameters, hyperrectangle, threshold, above_threshold, only_check_hypothesis = True):
        logger.info("Check region via stormpy")
        assert only_check_hypothesis

        # Initialize PLA checker
        pla_checker = self.get_pla_checker(threshold)
        model_parameters = self.get_model().collect_probability_parameters()
        # Set region
        region_string = hyperrectangle.to_region_string(parameters)
        logger.debug("Region string is {}".format(region_string))
        region = stormpy.pars.ParameterRegion(region_string, model_parameters)
        # Check via PLA
        logger.info("Call stormpy for PLA check")
        hypothesis = stormpy.pars.RegionResultHypothesis.ALLVIOLATED if above_threshold else stormpy.pars.RegionResultHypothesis.ALLSAT
        start = time.time()
        result = pla_checker.check_region(self._environment, region, hypothesis, stormpy.pars.RegionResult.UNKNOWN,
                                          False)
        duration = time.time() - start
        self._pla_checker_time += duration
        self._regions_checked += 1
        logger.info("Stormpy call finished successfully with result: {} and took {} s".format(result, duration))

        if result == stormpy.pars.RegionResult.ALLSAT:
            if hypothesis == stormpy.pars.RegionResultHypothesis.ALLSAT:
                region_result = RegionCheckResult.Satisfied
            else:
                assert hypothesis == stormpy.pars.RegionResultHypothesis.ALLVIOLATED
                raise RuntimeError("Contradiction of hypothesis")
        elif result == stormpy.pars.RegionResult.ALLVIOLATED:
            if hypothesis == stormpy.pars.RegionResultHypothesis.ALLVIOLATED:
                region_result = RegionCheckResult.Satisfied
            else:
                assert hypothesis == stormpy.pars.RegionResultHypothesis.ALLSAT
                raise RuntimeError("Contradiction of hypothesis")
        elif result == stormpy.pars.RegionResult.UNKNOWN:
            region_result = RegionCheckResult.Unknown
        elif result == stormpy.pars.RegionResult.EXISTSBOTH:
            raise RuntimeError("Unexpected outcome, something went wrong.")
        elif result == stormpy.pars.RegionResult.CENTERSAT or result == stormpy.pars.RegionResult.CENTERVIOLATED:
            logger.warning("Center sat/violated is not expected.")
            region_result = RegionCheckResult.Unknown
        else:
            raise RuntimeError("Unexpected result '{}'".format(result))

        region = HyperRectangle.from_region_string(region_string, parameters)
        regions = [(region_result, region)]
        return regions

    def bound_value_in_hyperrectangle(self, parameters, hyperrectangle, direction, all_states=False, generate_split_estimates=False):
        """
        
        :param parameters: The parameters
        :param hyperrectangle: The hyperrectangle for the parameters
        :param direction: 
        :param all_states: Should the value be computed for all states
        :return: 
        """
        # TODO support for exact PLA.
        logger.debug("Bound values: Obtain PLA checker")
        pla_checker = self.get_pla_checker(None, splitting_assistance=generate_split_estimates, allow_simplifications=(not all_states))
        mapping = self.get_parameter_mapping(parameters, from_storm=True)
        region_string = hyperrectangle.to_region_string(parameters)
        vars = self.get_model().collect_probability_parameters()
        vars.update(self.get_model().collect_reward_parameters())
        par_region = stormpy.pars.ParameterRegion(region_string, vars)
        if all_states:
            logger.debug("Bound for all states")
            return pla_checker.get_bound_all_states(
                self._environment, par_region,direction), dict([[mapping[x].id, val] for x, val in pla_checker.get_split_suggestion().items()]) if generate_split_estimates else None
        else:
            logger.debug("Bound for initial state")
            result = pla_checker.get_bound(self._environment, par_region, direction)
            assert result.is_constant()
            return stormpy.convert_from_storm_type(result.constant_part()), dict([[mapping[x].id, val] for x, val in pla_checker.get_split_suggestion().items()]) if generate_split_estimates else None

    def prob01_states(self):
        logger.debug("Compute prob01 states")
        model = self.get_model()
        formula = self.pctlformula[0].raw_formula
        assert type(formula) == stormpy.logic.ProbabilityOperator
        path_formula = formula.subformula
        if type(path_formula) == stormpy.logic.EventuallyFormula:
            phi_formula = stormpy.logic.BooleanLiteralFormula(True)
            psi_formula = path_formula.subformula
        elif type(path_formula) == stormpy.logic.UntilFormula:
            phi_formula = path_formula.left_subformula
            psi_formula = path_formula.right_subformula
        else:
            raise ValueError("Property type not supported")
        phi_result = stormpy.model_checking(model, phi_formula)
        phi_states = phi_result.get_truth_values()
        psi_result = stormpy.model_checking(model, psi_formula)
        psi_states = psi_result.get_truth_values()
        if model.model_type == stormpy.storage.ModelType.DTMC:
            (prob0, prob1) = stormpy.compute_prob01_states(model, phi_states, psi_states)
        elif model.model_type == stormpy.storage.ModelType.MDP:
            assert self.pctlformula[0].raw_formula.has_optimality_type
            assert self.pctlformula[0].raw_formula.optimality_type in [stormpy.OptimizationDirection.Minimize, stormpy.OptimizationDirection.Maximize]
            if self.pctlformula[0].raw_formula.optimality_type == stormpy.OptimizationDirection.Minimize:
                (prob0, prob1) = stormpy.compute_prob01min_states(model, phi_states, psi_states)
            else:
                (prob0, prob1) = stormpy.compute_prob01max_states(model, phi_states, psi_states)
        return prob0, prob1

    def rew0_states(self):
        formula = self.pctlformula[0].raw_formula
        assert type(formula) == stormpy.logic.RewardOperator
        path_formula = formula.subformula
        if type(path_formula) == stormpy.logic.EventuallyFormula:
            psi_formula = path_formula.subformula
        else:
            raise ValueError("Property type not supported")
        psi_result = stormpy.model_checking(self.get_model(), psi_formula)
        psi_states = psi_result.get_truth_values()
        return psi_states
