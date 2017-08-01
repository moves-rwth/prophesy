from enum import Enum
from abc import ABCMeta, abstractmethod


class ProblemDescription:
    def __init__(self, solutionfunction=None, model=None, property=None, wd_constraints=None, gp_constraints=None):
        """
        Constructor.
        :param solutionfunction: Rational function representing reachability probability.
        :param model: Model.
        :param property: Property.
        :param wd_constraints: Constraints for well formedness.
        :param gp_constraints: Constraints for graph preservation.
        """
        self.solutionfunction = solutionfunction
        self.model = model
        self.property = property
        self.welldefined_constraints = wd_constraints
        self.graph_preserving_constraints = gp_constraints


class RegionCheckResult(Enum):
    """
    Result of region check (counterexample, satisfied, refined, unkown).
    """
    CounterExample = 0  #: The region does not satisfy the property; we found a counterexample
    Satisfied = 1  #: The region satisfies the property.
    Refined = 2  #: We don't know, we return a subregion which is still undecided. The remainder is satisfied.
    unknown = 3  #: We don't know.


class RegionChecker:
    """
    Interface for region checkers.
    """

    __metaclass__ = ABCMeta

    @abstractmethod
    def __init__(self, backend, parameters):
        """
        Constructor.
        :param backend: Backend to use for checking regions.
        :param parameters: The parameters of the problem.
        :type parameters: ParameterOrder.
        """
        raise NotImplementedError("Abstract function called")

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
    def print_info(self):
        """
        Print information about region checking.
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
