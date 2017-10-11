from enum import Enum
from abc import ABCMeta, abstractmethod


class ProblemDescription:
    def __init__(self, solutionfunction=None, parameters=None, model=None, property=None, wd_constraints=None,
                 gp_constraints=None, threshold=None, samples=None):
        """
        Constructor.
        :param solutionfunction: Rational function representing reachability probability.
        :param parameters: Parameters occuring in model and solution function.
        :param model: Model.
        :param property: Property.
        :param wd_constraints: Constraints for well formedness.
        :param gp_constraints: Constraints for graph preservation.
        """
        self.solutionfunction = solutionfunction
        self.parameters = parameters
        self.model = model
        self.property = property
        self.welldefined_constraints = wd_constraints
        self.graph_preserving_constraints = gp_constraints
        self.samples = samples
        self.threshold = threshold


class RegionCheckResult(Enum):
    """
    Result of region check (counterexample, satisfied, refined, unknown).
    """
    CounterExample = 0  #: The region does not satisfy the property; we found a counterexample
    Satisfied = 1  #: The region satisfies the property.
    Refined = 2  #: We don't know, we return a subregion which is still undecided. The remainder is satisfied.
    Unknown = 3  #: We don't know.


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

    def print_info(self):
        i = 1
        print("no.  result          time    tot. time  area   tot. area")
        total_sec = 0
        total_area = 0
        for benchmark in self.benchmark_output:
            total_sec = total_sec + benchmark[1]
            if benchmark[0] == RegionCheckResult.Satisfied:
                total_area = total_area + benchmark[2]
            print("{:3}  {:14s}  {:5.2f}s    {:6.2f}s  {:4.3f}      {:4.3f}".format(i, benchmark[0].name, benchmark[1],
                                                                                    total_sec, float(benchmark[2]),
                                                                                    float(total_area)))
            i = i + 1

    @abstractmethod
    def analyse_region(self, region, safe):
        """
        Analyse the given region and return the result (and a counterexample point if found).
        :param region: Region as either HyperRectangle or shapely Polygon.
        :param safe: Boolean to indicate if the region should be considered as safe or unsafe.
        :return Tuple (RegionCheckResult, counterexample point).
        """
        raise NotImplementedError("Abstract function called")
