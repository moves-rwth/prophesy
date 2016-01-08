from abc import ABCMeta, abstractmethod


from modelcheckers.pmc import ProbabilisticModelChecker


class ParametricProbabilisticModelChecker(ProbabilisticModelChecker):
    __metaclass__ = ABCMeta



    @abstractmethod
    def getRationalFunction(self):
        raise NotImplementedError
