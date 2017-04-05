from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.modelcheckers.pmc import BisimulationType
from prophesy.config import configuration
from prophesy.exceptions.module_error import ModuleError
from prophesy.exceptions.configuration_error import ConfigurationError
from prophesy.sampling.sampler import Sampler
from prophesy.input.prismfile import PrismFile
from prophesy.input.resultfile import ParametricResult

import pycarl
import pycarl.formula


if not configuration.is_module_available("stormpy"):
    raise ModuleError("Module stormpy is needed for using the Python API for Storm. Maybe your config is outdated?")
else:
    import stormpy.info
    import stormpy.logic
    import stormpy.core


class StormpyModelChecker(ParametricProbabilisticModelChecker, Sampler):
    """This is the python interface class to use the Storm Modelchecker"""

    def __init__(self):
        """Initializes the Modelchecker with standard values."""
        self.bisimulation = BisimulationType.strong
        self.pctl_formula = None
        self.prism_file = None
        self.program = None
        self.last_result = None

    def name(self):
        """Returns a string representation of the models name."""
        return "stormpy"

    def version(self):
        """ Returns the current storm version."""
        return str(stormpy.info.Version.short)

    def set_pctl_formula(self, formula):
        """Sets the pctl-formular to modelcheck the current model with that formula. The formula is directly parsed."""
        if self.program == None:
            # Otherwise we cannot parse all kind of formulae.
            raise NotEnoughInformationError("Stormpy requires the program before the formula can be loaded.")

        if self.program is not None:
            self.pctl_formula = stormpy.parse_properties_for_prism_program(formula, self.program)

    def load_model_from_prismfile(self, p_file):
        """ Load a model encrypted in prism file format."""
        self.prism_file = p_file
        self.program = stormpy.parse_prism_program(self.prism_file.location)

    def set_bisimulation(self, type):
        """Sets the bisimulation type for Strom. Raises a ConfigurationError, if the type is not valid."""
        if type < 0 or type > 3:
            raise ConfigurationError("Bisimulationtype not valid.")
        else:
            self.bisimulation = type

    def sample(self, samplepoints):
        raise NotImplementedError

    def get_rational_function(self):
        """This method returns the rational function as the result from the model checking task."""
        if self.prism_file.nr_parameters() == 0:
            model = stormpy.build_model(self.program)
        else:
            model = stormpy.build_parametric_model(self.program, self.pctl_formula)
            print(model.labels)
        result = stormpy.model_checking(model, self.pctl_formula[0])

        return ParametricResult(self.prism_file.parameters,
                                list(result.constraints_graph_preserving) + list(result.constraints_well_formed),
                                result.result_function)
