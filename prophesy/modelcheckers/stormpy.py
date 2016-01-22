from modelcheckers.ppmc  import ParametricProbabilisticModelChecker
from modelcheckers.pmc import BisimulationType
from config import configuration

if not configuration.is_module_available("stormpy"):
    raise ModuleError("Module stormpy is needed for using the Python API for Storm")
else:
    import stormpy.info
    import stormpy.logic
    import stormpy.core

class StormpyModelChecker(ParametricProbabilisticModelChecker):
    def __init__(self):
        self.bisimulation = BisimulationType.strong
        self.pctl_formula = None
        self.prism_file = None
        self.program = None
        stormpy.core.set_up("")

    def name(self):
        return "stormpy"

    def version(self):
        return stormpy.info.Version.short()


    def set_pctl_formula(self, formula):
        if self.program == None:
            raise NotEnoughInformationError("Stormpy requires the program before the formula can be loaded.")
        self.pctl_formula = stormpy.core.parse_formulae(formula, self.program)

    def load_model_from_prismfile(self, prismfile):
        self.prism_file = prismfile
        self.program = stormpy.core.parse_program(prismfile.location)


    def set_bisimulation(self, BisimulationType): raise NotImplementedError

    def uniform_sample(self, ranges): raise NotImplementedError

    def sample(self, samplePoints): raise NotImplementedError

    def get_rational_function(self):
        model = None
        if self.prism_file.nr_parameters() == 0:
            model = stormpy.core.buildModelFromPrismProgram(self.program, self.pctl_formula)
        else:
            model = stormpy.core.build_model(self.program, self.pctl_formula[0])
            pdtmc = model.as_pdtmc()

        return stormpy.core.perform_state_elimination(pdtmc, self.pctl_formula[0])

