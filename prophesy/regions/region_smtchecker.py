import time

from prophesy.regions.region_checker import RegionChecker, RegionCheckResult
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.smt.smt import Answer
from abc import abstractmethod
import prophesy.adapter.pycarl as pc


class SmtRegionChecker(RegionChecker):
    def __init__(self, backend):
        """
        Constructor.
        :param backend: Smt solver to check regions
        :type backend: SMTSolver
        """
        super().__init__()
        self._smt2interface = backend
        self.parameters = None
        self._safe_relation = pc.Relation.GEQ
        self._bad_relation = pc.Relation.LESS

    @abstractmethod
    def initialize(self, problem_description, threshold, constants=None):
        raise NotImplementedError("Calling an abstract method")

    @abstractmethod
    def _evaluate(self, smt_model):
        """
        Takes the smt_model, creates a counterexample.
        
        :param smt_model: 
        :return: 
        """
        raise RuntimeError("Abstract method called")

    def analyse_region(self, polygon, safe):
        """
        Extends the current area by using the new polygon
        regions are the newly added regions for the polygon
        polygon marks the new area to cover
        safe indicates whether the area is safe or bad
        returns tuple (valid constraint, polygon/counterexample point)
        if constraint is valid the tuple  is (True, polygon added)
        if constraint is invalid the tuple is (False, point as counterexample)
        
        :param polygon: either HyperRectangle or shapely Polygon
        :param safe: Boolean to indicate if the region should be considered as safe or unsafe
        """
        smt_successful = False
        smt_model = None

        if isinstance(polygon, HyperRectangle):
            constraint = polygon.to_formula(self.parameters)
        else:
            raise RuntimeError("Unexpected type of region.")

        while not smt_successful:
            # check constraint with smt
            with self._smt2interface as smt_context:
                smt_context.assert_constraint(constraint)

                # Invert the safe flag to try and find a counter example
                smt_context.set_guard("__safe", not safe)
                smt_context.set_guard("__bad", safe)

                start = time.time()
                checkresult = smt_context.check()
                duration = time.time() - start

                if checkresult == Answer.unsat:
                    checkresult = RegionCheckResult.Satisfied
                if checkresult == Answer.sat:
                    checkresult = RegionCheckResult.CounterExample
                if isinstance(polygon, HyperRectangle):
                    self.benchmark_output.append((checkresult, duration, polygon.size()))
                else:
                    self.benchmark_output.append((checkresult, duration, polygon.area))
                if checkresult not in [RegionCheckResult.Satisfied, RegionCheckResult.CounterExample]:
                    break
                else:
                    if checkresult == RegionCheckResult.CounterExample:
                        smt_model = smt_context.get_model()
                    break

        if checkresult == RegionCheckResult.Satisfied:
            return RegionCheckResult.Satisfied, None
        elif checkresult == RegionCheckResult.CounterExample:
            return RegionCheckResult.CounterExample, self._evaluate(smt_model)
        else:
            # SMT failed completely
            return RegionCheckResult.Unknown, None
