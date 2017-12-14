import logging

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
        self._welldefined_checker = None
        # Storing objects of stormpy for incremental calls
        self._program = None
        self._model = None
        self._parameter_constraints = None
        self._graph_preservation_constraints = None
        self._parameter_mapping = None
        self._model_instantiator = None
        self._pla_checker = None
        self._pla_threshold = None
        self._environment = stormpy.Environment()

    def name(self):
        return "stormpy"

    def version(self):
        return str(stormpy.info.Version.short)

    def set_pctl_formula(self, formula):
        if self._program is None:
            logger.debug("Load formula without a program.")
            self.pctlformula = stormpy.parse_properties(str(formula))
        else:
            logger.debug("Load formula with respect to program.")
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
        self._model_instantiator = None
        self._pla_checker = None
        self._welldefined_checker = None

    def set_welldefined_checker(self, checker):
        self._welldefined_checker = checker

    def load_model_from_drn(self, drnfile, constants=Constants()):
        self._reset_internal()
        self.drnfile = drnfile
        self.constants = constants

    def load_model_from_prismfile(self, prism_file, constants=Constants()):
        logger.debug("Load model from prism file")
        self._reset_internal()
        self.prismfile = prism_file
        self.constants = constants
        prismcompatibility = True if self.prismfile.model_type == ModelType.CTMC else False
        self._program = stormpy.parse_prism_program(self.prismfile.location, prismcompatibility)

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

            if self.bisimulation == stormpy.BisimulationType.STRONG or self.bisimulation == stormpy.BisimulationType.WEAK:
                logger.info("Perform bisimulation")
                self._model = stormpy.perform_bisimulation(self._model, self.pctlformula, self.bisimulation)
        return self._model

    def get_parameter_mapping(self, prophesy_parameters):
        """Get a mapping from prophesy parameters to model parameters in stormpy."""

        def get_matching_model_parameter(model_parameters, variable_name):
            """Return matching parameter or None."""
            return next((v for v in model_parameters if v.name == variable_name), None)

        if self._parameter_mapping is None:
            self._parameter_mapping = {}
            model_parameters = self.get_model().collect_probability_parameters() | self.get_model().collect_reward_parameters()
            for parameter in prophesy_parameters:
                model_param = get_matching_model_parameter(model_parameters, parameter.name)
                assert model_param is not None
                self._parameter_mapping[parameter] = model_param

        for parameter in prophesy_parameters:
            assert parameter in self._parameter_mapping
        return self._parameter_mapping

    def get_parameter_constraints(self):
        if self._parameter_constraints is None or self._graph_preservation_constraints is None:
            # Collect constraints if not already there
            logger.info("Call stormpy for constraints")

            collector = stormpy.ConstraintCollector(self.get_model())
            self._parameter_constraints = []
            self._graph_preservation_constraints = []
            # Convert formulas to gmp
            for formula in collector.wellformed_constraints:
                assert formula.type == pc.FormulaType.CONSTRAINT
                converted_formula = pc.Formula(pc.convert_from_storm_type(formula.get_constraint()))
                self._parameter_constraints.append(converted_formula)
            for formula in collector.graph_preserving_constraints:
                assert formula.type == pc.FormulaType.CONSTRAINT
                converted_formula = pc.Formula(pc.convert_from_storm_type(formula.get_constraint()))
                self._graph_preservation_constraints.append(converted_formula)
            logger.info("Stormpy call finished")

        return self._parameter_constraints, self._graph_preservation_constraints

    def get_model_instantiator(self):
        """
        Return model instantiator.
        :return: Model instantiator.
        """
        if self._model_instantiator is None:
            self._model_instantiator = stormpy.pars.PDtmcInstantiator(self.get_model())
        return self._model_instantiator

    def get_pla_checker(self, threshold):
        """
        Return model checker for PLA.
        :param threshold: Threshold in formula.
        :return: PLA model checker.
        """
        if self._pla_checker is None or self._pla_threshold != threshold:
            self._pla_threshold = threshold
            # Set formula for PLA
            formula = self.pctlformula[0].raw_formula
            if threshold is not None:
                expression_manager = stormpy.ExpressionManager()
                expression = expression_manager.create_rational(pc.convert_from_storm_type(threshold))
                formula.set_bound(stormpy.logic.ComparisonType.LESS, expression)
            # Create PLA checker
            self._pla_checker = stormpy.pars.create_region_checker(self._environment, self.get_model(), formula)
        return self._pla_checker

    def get_rational_function(self):
        self.get_model()
        # Compute rational function
        logger.info("Compute solution function")
        rational_function = pc.convert_from_storm_type(
            stormpy.model_checking(self._model, self.pctlformula[0]).at(self._model.initial_states[0]))
        logger.info("Stormpy model checking finished successfully")

        # Collect constraints
        parameter_constraints, graph_preservation_constraints = self.get_parameter_constraints()

        return ParametricResult(self.prismfile.parameters, parameter_constraints, graph_preservation_constraints,
                                rational_function)

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
        model_instantiator = self.get_model_instantiator()
        point = {parameter_mapping[parameter]: pc.convert_to_storm_type(val) for parameter, val in
                 parameter_instantiation.items()}
        instantiated_model = model_instantiator.instantiate(point)
        result = pc.convert_from_storm_type(
            stormpy.model_checking(instantiated_model, self.pctlformula[0]).at(instantiated_model.initial_states[0]))
        return result

    def check_hyperrectangle(self, parameters, hyperrectangle, threshold, above_threshold):
        logger.info("Check region via stormpy")

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
        result = pla_checker.check_region(self._environment, region, hypothesis, stormpy.pars.RegionResult.UNKNOWN,
                                          False)
        logger.info("Stormpy call finished successfully with result: {}".format(result))

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

    def bound_value_in_hyperrectangle(self, parameters, hyperrectangle, direction):
        pla_checker = self.get_pla_checker(None)
        region_string = hyperrectangle.to_region_string(parameters)
        result = pla_checker.get_bound(
            stormpy.pars.ParameterRegion(region_string, self.get_model().collect_probability_parameters()), direction)
        assert result.is_constant()
        return stormpy.convert_from_storm_type(result.constant_part())
