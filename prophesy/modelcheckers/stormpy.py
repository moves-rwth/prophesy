import logging

from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.modelcheckers.pmc import BisimulationType
from prophesy.config import configuration
from prophesy.exceptions.module_error import ModuleError
from prophesy.exceptions.configuration_error import ConfigurationError
from prophesy.sampling.sampler import Sampler
from prophesy.input.prismfile import PrismFile
from prophesy.input.solutionfunctionfile import ParametricResult
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError

logger = logging.getLogger(__name__)


if not configuration.is_module_available("stormpy"):
    raise ModuleError("Module stormpy is needed for using the Python API for Storm. Maybe your config is outdated?")
else:
    import stormpy
    import stormpy.info
    import stormpy.logic


class StormpyModelChecker(ParametricProbabilisticModelChecker):
    """This is the python interface class to use the Storm Modelchecker"""

    def __init__(self):
        """Initializes the Modelchecker with standard values."""
        self.bisimulation = BisimulationType.strong
        self.pctl_formula = None
        self.prism_file = None
        self.constants = None
        self.program = None
        self.last_result = None
        self.model = None

    def name(self):
        """Returns a string representation of the models name."""
        return "stormpy"

    def version(self):
        """ Returns the current storm version."""
        return str(stormpy.info.Version.short)

    def set_pctl_formula(self, formula):
        """Sets the pctl-formular to modelcheck the current model with that formula. The formula is directly parsed."""
        #TODO instead of going via string, do a bit more meaningful stuff.
        if self.program == None:
            self.pctl_formula = stormpy.parse_properties(str(formula))
        else:
            self.pctl_formula = stormpy.parse_properties_for_prism_program(str(formula), self.program)

    def load_model_from_prismfile(self, p_file, constants):
        """ Load a model encrypted in prism file format."""
        self.prism_file = p_file
        self.constants = constants
        #TODO use constants here.
        self.program = stormpy.parse_prism_program(self.prism_file.location)

    def set_bisimulation_type(self, type):
        """Sets the bisimulation type for Storm. Raises a ConfigurationError, if the type is not valid."""
        if type < 0 or type > 3:
            raise ConfigurationError("Bisimulationtype not valid.")
        else:
            self.bisimulation = type

    def _build_model(self):
        if self.prism_file.nr_parameters() == 0:
            assert not self.program.has_undefined_constants
            self.model = stormpy.build_model(self.program, self.pctl_formula)
        else:
            assert self.program.has_undefined_constants
            self.model = stormpy.build_parametric_model(self.program, self.pctl_formula)

    def perform_sampling(self, samplepoints):
        if self.model is None:
            self._build_model()
        for sample in samplepoints:
            pass
        raise NotImplementedError("Implementation not yet done.")

    def get_rational_function(self):
        """This method returns the rational function as the result from the model checking task."""
        if self.model is None:
            self._build_model()

        result = stormpy.model_checking(self.model, self.pctl_formula[0])
        initial_state = self.model.initial_states[0]
        result = result.at(initial_state)
        constraints = []
        # TODO set constraints (graph_preserving and well_formed
        return ParametricResult(self.prism_file.parameters, constraints, result)
