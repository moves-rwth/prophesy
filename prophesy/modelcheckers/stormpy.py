
#import stormpy
#import stormpy.info

from modelcheckers.ppmc  import ParametricProbabilisticModelChecker
from modelcheckers.pmc import BisimulationType

class StormpyModelChecker(ParametricProbabilisticModelChecker):
    def __init__(self):
        self.bisimulation = BisimulationType.strong

    def name(self):
        return "stormpy"

    def version(self):
        return stormpy.info.Version.short()


    def set_pctl_formula(self, formula): raise NotImplementedError

    def load_model_from_prismfile(self, prismfile): raise NotImplementedError

    def set_bisimulation(self, BisimulationType): raise NotImplementedError

    def uniform_sample(self, ranges): raise NotImplementedError

    def sample(self, samplePoints): raise NotImplementedError

    def get_rational_function(self): raise NotImplementedError
