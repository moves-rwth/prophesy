from abc import ABCMeta, abstractmethod
from enum import Enum

from prophesy.sampling.sampler import Sampler
from prophesy.input.modelfile import PrismFile, DrnFile
from prophesy.data.constant import Constants

class BisimulationType(Enum):
    """
    Bisimulation type (None, Strong, Weak).
    """
    none = 0
    strong = 1
    weak = 2


class ProbabilisticModelChecker(Sampler):
    """
    An abstraction of probabilistic model checkers for concrete systems.
    """
    __metaclass__ = ABCMeta

    @abstractmethod
    def name(self):
        """
        Get name of model checker.
        :return: A string with the name of the model checker.
        """
        raise NotImplementedError("Abstract function called")

    @abstractmethod
    def version(self):
        """
        Get version of model checker.
        :return: A string with the version of the model checker.
        """
        raise NotImplementedError("Abstract function called")

    @abstractmethod
    def set_pctl_formula(self, formula):
        """
        Set PCTL formula to check.
        :param formula: PCTL formula
        """
        raise NotImplementedError("Abstract function called")

    def load_model(self, model_description, constants=Constants()):
        """
        
        :param model_description: 
        :param constants: 
        :return: 
        """
        if isinstance(model_description, DrnFile):
            return self.load_model_from_drn(model_description, constants)
        elif isinstance(model_description, PrismFile):
            return self.load_model_from_prismfile(model_description, constants)

    @abstractmethod
    def load_model_from_drn(self, drnfile, constants=Constants()):
        raise NotImplementedError("Abstract function called")

    @abstractmethod
    def load_model_from_prismfile(self, prismfile, constants=Constants()):
        """
        Load model from given Prism file.
        :param prismfile: Prism file.
        :param constants: List of constants and their values.
        """
        raise NotImplementedError("Abstract function called")

    @abstractmethod
    def set_bisimulation_type(self, bisimulationType):
        """
        Set bisimulation type.
        :param bisimulationType: Bisimulation type (None, Strong, Weak).
        """
        raise NotImplementedError("Abstract function called")
