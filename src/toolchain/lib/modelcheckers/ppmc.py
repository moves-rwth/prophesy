from abc import ABCMeta, abstractmethod

class ParametricProbablisticModelChecker():
    __metaclass__ = ABCMeta

    @abstractmethod
    def name(self): raise NotImplementedError

    @abstractmethod
    def version(self): raise NotImplementedError

    @abstractmethod
    def get_rational_function(self, prism_file, pctl_file): raise NotImplementedError
        
        
        
