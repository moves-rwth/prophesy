from enum import Enum
from abc import ABCMeta, abstractmethod


class RegionCheckResult(Enum):
    """
    Result of region check (counterexample, satisfied, refined, homogeneous, unknown).
    """
    CounterExample = 0  #: The region does not satisfy the property; we found a counterexample
    Satisfied = 1  #: The region satisfies the property.
    Refined = 2  #: We don't know, we return a subregion which is still undecided. The remainder is satisfied.
    Splitted =3  #: We don't know, but we found subregions ourselves that are safe/unsafe, and subregions that remain
    Homogenous =  4 #: All the same color.
    Inhomogenous = 5 #: Contains a border point
    Unknown = 6  #: We don't know.

    def __str__(self):
        names = ["RCR:Cex", "RCR:Sat", "RCR:Ref", "RCR:Split", "RCR:Hom", "RCR:Inhom", "RCR:Unk"]
        assert self.value < len(names)
        return names[self.value]


class RegionChecker:
    """
    Interface for region checkers.
    """

    __metaclass__ = ABCMeta

    @abstractmethod
    def __init__(self):
        """
        Constructor.
        :param backend: Backend to use for checking regions.
        :param parameters: The parameters of the problem.
        :type parameters: ParameterOrder.
        """
        self.benchmark_output = []
        self.support_nongraphpreserving = False

    def supports_only_closed_regions(self):
        return False

    @abstractmethod
    def initialize(self, problem_description, threshold, constants=None):
        """
        Initialize region checker.
        :param problem_description: Data for problem (model, property, solution function).
        :type problem_description: ProblemDescription.
        :param threshold: Threshold.
        :param constants: Constants in model file.
        """
        raise NotImplementedError("Abstract function called")


    @abstractmethod
    def analyse_region(self, region, safe):
        """
        Analyse the given region and return the result (and a counterexample point if found).
        :param region: Region as either HyperRectangle or shapely Polygon.
        :param safe: Boolean to indicate if the region should be considered as safe or unsafe.
        :return Tuple (RegionCheckResult, counterexample point).
        """
        raise NotImplementedError("Abstract function called")
