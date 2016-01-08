import stormpy
import stormpy.info

class StormpyModelChecker(ParametricProbabilisticModelChecker, ProbabilisticModelChecker):
    def __init__(self):
        self.bisimulation = BisimulationType.strong

    def name(self):
        return "stormpy"

    def version(self):
        return stormpy.info.Version.short()

    def set_bisimulation_type(self, t):
        pass

    def set_pctl_formula(self, formula):
        pass

    def sample_pctl_formula(self, prism_filepath, pctl_filepath, samplepoints):
        pass
