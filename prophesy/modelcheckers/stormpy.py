import logging

from prophesy.config import configuration
from prophesy.exceptions.module_error import ModuleError
from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.modelcheckers.pmc import BisimulationType
from prophesy.exceptions.configuration_error import ConfigurationError
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError
from prophesy.input.solutionfunctionfile import ParametricResult
from prophesy.data.samples import InstantiationResultDict, InstantiationResult
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

        self.bisimulation = BisimulationType.strong
        self.pctl_formula = None
        self.prism_file = None
        self.constants = None
        self.program = None
        self.last_result = None
        self.model = None

    def name(self):
        return "stormpy"

    def version(self):
        return str(stormpy.info.Version.short)

    def set_pctl_formula(self, formula):
        # TODO instead of going via string, do a bit more meaningful stuff.
        if self.program is None:
            self.pctl_formula = stormpy.parse_properties(str(formula))
        else:
            self.pctl_formula = stormpy.parse_properties_for_prism_program(str(formula), self.program)

    def load_model_from_prismfile(self, p_file, constants):
        self.prism_file = p_file
        self.constants = constants
        # TODO use constants here.
        self.program = stormpy.parse_prism_program(self.prism_file.location)

    def set_bisimulation_type(self, bisimulationType):
        if bisimulationType < 0 or bisimulationType > 3:
            raise ConfigurationError("Bisimulationtype not valid.")
        else:
            self.bisimulation = bisimulationType

    def build_model(self):
        """
        Build prism model.
        """
        logger.info("Build model")

        if self.prism_file is None:
            raise NotEnoughInformationError("Prism model not set.")
        if self.pctl_formula is None:
            raise NotEnoughInformationError("PCTL formula not set.")

        if self.prism_file.nr_parameters() == 0:
            assert not self.program.has_undefined_constants
            self.model = stormpy.build_model(self.program, self.pctl_formula)
        else:
            assert self.program.has_undefined_constants
            self.model = stormpy.build_parametric_model(self.program, self.pctl_formula)

    def check_model(self, model, property):
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

    def get_rational_function(self):
        if self.model is None:
            self.build_model()

        # Compute rational function
        logger.info("Compute solution function")
        rational_function = self.check_model(self, model, self.pctl_formula[0])
        logger.info("Stormpy model checking finished successfully")

        # Collect constraints
        collector = stormpy.ConstraintCollector(self.model)
        parameter_constraints = []
        graph_preservation_constraints = []
        # Convert formulas to gmp
        for formula in collector.wellformed_constraints:
            assert formula.type == pc.FormulaType.CONSTRAINT
            converted_formula = pc.Formula(pc.convert_from(formula.get_constraint()))
            parameter_constraints.append(converted_formula)
        for formula in collector.graph_preserving_constraints:
            assert formula.type == pc.FormulaType.CONSTRAINT
            converted_formula = pc.Formula(pc.convert_from(formula.get_constraint()))
            graph_preservation_constraints.append(converted_formula)

        return ParametricResult(self.prism_file.parameters, parameter_constraints, graph_preservation_constraints,
                                rational_function)

    def perform_sampling(self, samplepoints, constants=None):
        if self.model is None:
            self.build_model()

        logger.info("Perform uniform sampling")

        # Initialize mapping from prophesy variables to model parameters in stormpy
        parameter_mapping = {}
        model_parameters = self.model.collect_probability_parameters()
        for parameter in samplepoints.parameters:
            param_string = str(parameter.variable)
            model_param = next((var for var in model_parameters if str(var) == param_string), None)
            assert model_param is not None
            parameter_mapping[parameter] = model_param

        # Perform sampling with model instantiator
        logger.info("Call stormpy for sampling")
        samples = InstantiationResultDict(samplepoints.parameters)
        instantiator = stormpy.pars.PDtmcInstantiator(self.model)

        for sample_point in samplepoints:
            point = {parameter_mapping[parameter]: pc.convert_to(val) for parameter, val in sample_point.items()}
            instantiated_model = instantiator.instantiate(point)
            result = self.check_model(instantiated_model, self.pctl_formula[0])
            samples.add_result(InstantiationResult(sample_point, result))

        logger.info("Sampling with stormpy successfully finished")
        return samples

    def check_hyperrectangle(self, parameter_ranges, threshold, hypothesis):
        raise NotImplementedError("Checking of hyperrectangles with stormpy is not implemented.")
