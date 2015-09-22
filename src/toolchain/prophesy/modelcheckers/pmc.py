from abc import ABCMeta, abstractmethod

class ProbablisticModelChecker():
    __metaclass__ = ABCMeta

    @abstractmethod
    def name(self): raise NotImplementedError

    @abstractmethod
    def version(self): raise NotImplementedError

    @abstractmethod
    def uniform_sample_pctl_formula(self, prism_file, pctl_file, parameters, ranges): raise NotImplementedError

    @abstractmethod
    def sample_pctl_formula(self, prism_file, pctl_file, parameters, points): raise NotImplementedError
