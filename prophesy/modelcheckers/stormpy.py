import logging

from prophesy.config import configuration
from prophesy.exceptions.module_error import ModuleError
from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.modelcheckers.pmc import BisimulationType
from prophesy.exceptions.configuration_error import ConfigurationError
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError
from prophesy.input.solutionfunctionfile import ParametricResult
from prophesy.data.constant import Constants
from prophesy.data.samples import InstantiationResultDict, InstantiationResult
from prophesy.regions.region_checker import RegionCheckResult
from prophesy.data.hyperrectangle import HyperRectangle
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
        if not configuration.is_module_available("stormpy"):
            raise ModuleError(
                "Module stormpy is needed for using the Python API for Storm. Maybe your config is outdated?")

        self.prismfile = None
        self.pctlformula = None
        self.constants = None
        self.bisimulation = stormpy.BisimulationType.STRONG
        # Storing objects of stormpy for incremental calls
        self._program = None
        self._model = None
        self._parameter_constraints = None
        self._graph_preservation_constraints = None
        self._parameter_mapping = None
        self._model_instantiator = None
        self._pla_checker = None
        self._pla_formula = None

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
        self._pla_formula = None


    def load_model_from_prismfile(self, prism_file, constants=Constants()):
        self.prismfile = prism_file
        self.constants = constants
        self._program = stormpy.parse_prism_program(self.prismfile.location)
        # Reset stormpy objects
        self._model = None
        self._parameter_constraints = None
        self._graph_preservation_constraints = None
        self._parameter_mapping = None
        self._model_instantiator = None
        self._pla_checker = None

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

            if self.prismfile is None:
                raise NotEnoughInformationError("Prism model not set.")
            if self.pctlformula is None:
                raise NotEnoughInformationError("PCTL formula not set.")
            if not self._program.undefined_constants_are_graph_preserving:
                raise RuntimeError("Given model file still contains undefined constants")

            if self.prismfile.nr_parameters() == 0:
                assert not self._program.has_undefined_constants
                self._model = stormpy.build_model(self._program, self.pctlformula)
            else:
                assert self._program.has_undefined_constants
                self._model = stormpy.build_parametric_model(self._program, self.pctlformula)

            if self.bisimulation == stormpy.BisimulationType.STRONG or self.bisimulation == stormpy.BisimulationType.WEAK:
                logger.info("Perform bisimulation")
                self._model = stormpy.perform_bisimulation(self._model, self.pctlformula, self.bisimulation)
        return self._model

    def get_parameter_mapping(self, prophesy_parameters):
        """
        Get a mapping from prophesy parameters to model parameters in stormpy.
        :param prophesy_parameters: Parameters in prophesy.
        :return: Mapping from prophesy parameters to model parameters.
        """
        if self._parameter_mapping is None:
            self._parameter_mapping = {}
            model_parameters = self.get_model().collect_probability_parameters()
            for parameter in prophesy_parameters:
                param_string = str(parameter.variable)
                model_param = next((var for var in model_parameters if str(var) == param_string), None)
                assert model_param is not None
                self._parameter_mapping[parameter] = model_param

        for parameter in prophesy_parameters:
            assert parameter in self._parameter_mapping
        return self._parameter_mapping

    @staticmethod
    def check_model(model, property):
        """
        Compute result of model checking.
        :param model: Model.
        :param property: Property.
        :return: Result (as gmp type).
        """
        result = stormpy.model_checking(model, property)
        result = result.at(model.initial_states[0])
        # Convert to gmp
        return pc.convert_from(result)

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
                converted_formula = pc.Formula(pc.convert_from(formula.get_constraint()))
                self._parameter_constraints.append(converted_formula)
            for formula in collector.graph_preserving_constraints:
                assert formula.type == pc.FormulaType.CONSTRAINT
                converted_formula = pc.Formula(pc.convert_from(formula.get_constraint()))
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

    def get_pla_checker(self, formula):
        """
        Return model checker for PLA.
        :param formula: Formula to check.
        :return: PLA model checker.
        """
        if self._pla_checker is None or self._pla_formula != formula:
            self._pla_formula = formula
            self._pla_checker = stormpy.pars.create_region_checker(self.get_model(), formula)
        return self._pla_checker

    def get_rational_function(self):
        # Compute rational function
        logger.info("Compute solution function")
        rational_function = StormpyModelChecker.check_model(self.get_model(), self.pctlformula[0])
        logger.info("Stormpy model checking finished successfully")

        # Collect constraints
        parameter_constraints, graph_preservation_constraints = self.get_parameter_constraints()

        return ParametricResult(self.prismfile.parameters, parameter_constraints, graph_preservation_constraints,
                                rational_function)

    def perform_sampling(self, samplepoints):
        # Perform sampling with model instantiator
        logger.info("Call stormpy for sampling")
        samples = InstantiationResultDict(samplepoints.parameters)
        parameter_mapping = self.get_parameter_mapping(samplepoints.parameters)
        model_instantiator = self.get_model_instantiator()
        for sample_point in samplepoints:
            # Instantiate point and check result
            point = {parameter_mapping[parameter]: pc.convert_to(val) for parameter, val in sample_point.items()}
            instantiated_model = model_instantiator.instantiate(point)
            result = StormpyModelChecker.check_model(instantiated_model, self.pctlformula[0])
            samples.add_result(InstantiationResult(sample_point, result))

        logger.info("Sampling with stormpy successfully finished")
        return samples

    def check_hyperrectangle(self, parameters, hyperrectangle, threshold, above_threshold):
        logger.info("Check region via stormpy")

        # Set threshold and bound in formula
        formula = self.pctlformula[0].raw_formula
        expression_manager = stormpy.ExpressionManager()
        expression = expression_manager.create_rational(pc.Rational(threshold))
        formula.set_bound(stormpy.logic.ComparisonType.GEQ if above_threshold else stormpy.logic.ComparisonType.LESS,
                          expression)

        # Initialize PLA checker
        pla_checker = self.get_pla_checker(formula)
        model_parameters = self.get_model().collect_probability_parameters()
        # Set region
        region_string = hyperrectangle.to_region_string(parameters.get_variables())
        logger.debug("Region string is {}".format(region_string))
        region = stormpy.pars.ParameterRegion(region_string, model_parameters)
        # Check via PLA
        logger.info("Call stormpy for PLA check")
        result = pla_checker.check_region(region, stormpy.pars.RegionResultHypothesis.ALLSAT,
                                          stormpy.pars.RegionResult.UNKNOWN, False)
        logger.info("Stormpy call finished successfully with result: {}".format(result))

        if result == stormpy.pars.RegionResult.ALLVIOLATED:
            raise RuntimeError("Contradiction of hypothesis")
        elif result == stormpy.pars.RegionResult.ALLSAT:
            region_result = RegionCheckResult.Satisfied
        elif result == stormpy.pars.RegionResult.EXISTSBOTH:
            raise RuntimeError("Unexpected outcome, something went wrong.")
        elif result == stormpy.pars.RegionResult.UNKNOWN:
            region_result = RegionCheckResult.unknown
        elif result == stormpy.pars.RegionResult.CENTERSAT or result == stormpy.pars.RegionResult.CENTERVIOLATED:
            logger.warning("Center sat is not expected.")
            region_result = RegionCheckResult.unknown
        else:
            raise RuntimeError("Unexpected result '{}'".format(result))

        region = HyperRectangle.from_region_string(region_string, parameters.get_variables())
        regions = [(region_result, region)]
        return regions
