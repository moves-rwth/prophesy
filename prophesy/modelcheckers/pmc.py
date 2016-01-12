from abc import ABCMeta, abstractmethod
from enum import Enum

class BisimulationType(Enum):
    none = 0
    strong = 1
    weak = 2


class ProbabilisticModelChecker:
    """
    An abstraction of probabilistic model checkers for concrete systems
    """
    __metaclass__ = ABCMeta

    @abstractmethod
    def name(self):
        """
        :return: A string with the name of the solver
        """
        raise NotImplementedError

    @abstractmethod
    def version(self):
        """
        :return: A string with the version of the solvers
        """
        raise NotImplementedError

    @abstractmethod
    def set_pctl_formula(self, formula): raise NotImplementedError

    @abstractmethod
    def load_model_from_prismfile(self, prismfile): raise NotImplementedError

    @abstractmethod
    def set_bisimulation(self, BisimulationType): raise NotImplementedError

    @abstractmethod
    def uniform_sample(self, ranges): raise NotImplementedError

    @abstractmethod
    def sample(self, samplePoints): raise NotImplementedError
