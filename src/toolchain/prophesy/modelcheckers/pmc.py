from abc import ABCMeta, abstractmethod
from enum import Enum

class BisimulationType(Enum):
    none = 0
    strong = 1
    weak = 2


class ProbabilisticModelChecker:
    __metaclass__ = ABCMeta

    @abstractmethod
    def name(self): raise NotImplementedError

    @abstractmethod
    def version(self): raise NotImplementedError

    @abstractmethod
    def set_pctl_formula(self, formula): raise NotImplementedError

    @abstractmethod
    def load_model_from_prismfile(self, path): raise NotImplementedError

    @abstractmethod
    def set_bisimulation(self, BisimulationType): raise NotImplementedError

    @abstractmethod
    def uniform_sample(self, parameters, ranges): raise NotImplementedError

    @abstractmethod
    def sample(self, samplePoints): raise NotImplementedError
