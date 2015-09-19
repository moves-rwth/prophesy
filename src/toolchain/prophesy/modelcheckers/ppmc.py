from abc import ABCMeta, abstractmethod
from enum import Enum


class BisimulationType(Enum):
    none = 0
    strong = 1
    weak = 2


class ParametricProbabilisticModelChecker:
    __metaclass__ = ABCMeta

    @abstractmethod
    def name(self):
        raise NotImplementedError

    @abstractmethod
    def version(self):
        raise NotImplementedError

    @abstractmethod
    def set_bisimulation_type(self, t):
        raise NotImplementedError

    @abstractmethod
    def get_rational_function(self, prism_file, pctl_file):
        raise NotImplementedError
