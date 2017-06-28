from abc import ABCMeta, abstractmethod

from prophesy.modelcheckers.pmc import ProbabilisticModelChecker


class ParametricProbabilisticModelChecker(ProbabilisticModelChecker):
    __metaclass__ = ABCMeta

    @abstractmethod
    def get_rational_function(self):
        """
        :return: A rational function in prophesy format
        """
        raise NotImplementedError

    @abstractmethod
    def check_hyperrectangle(self, parameter_ranges, threshold, hypothesis):
        """
        :param parameter_ranges: A dictionary of variable name to its interval
        :param hypothesis: Whether the rectangle is expected to be above or below the given threshold
        :param threshold: A value indicating the threshold, that is, a value expected to be
                          above or below each value in the hyperrectangle
        :return: True iff the hypothesis holds
        """
        raise NotImplementedError
