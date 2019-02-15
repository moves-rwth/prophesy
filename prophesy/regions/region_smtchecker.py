import time
import logging

from prophesy.regions.region_checker import RegionChecker, RegionCheckResult
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.smt.smt import Answer
from abc import abstractmethod
import prophesy.adapter.pycarl as pc

logger = logging.getLogger(__name__)

class Context:
    def __init__(self, smt_context, fd):
        self.smt_context = smt_context
        self.fd = fd

    def __enter__(self):
        self.smt_context.push()
        return self

    def __exit__(self, type, value, tb):
        self.smt_context.pop()

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

        self._equals_relation = pc.Relation.EQ

        self._solver_timer = 0

        self._encoding_timer = 0

        self._fixed_direction = None


    @property
    def encoding_timer(self):
        return self._encoding_timer

    @abstractmethod
    def over_approximates(self):
        raise NotImplementedError("Calling an abstract method")

    @abstractmethod
    def initialize(self, problem_description, threshold, constants=None):
        raise NotImplementedError("Calling an abstract method")

    def _getsolver(self, safe):
        return Context(self._smt2interface, self._fixed_direction)

    @abstractmethod
    def _evaluate(self, smt_model):
        """
        Takes the smt_model, creates a counterexample.
        
        :param smt_model: 
        :return: 
        """
        raise RuntimeError("Abstract method called")

    @property
    def solver_timer(self):
        return self._solver_timer

    def analyse_region(self, polygon, safe, check_for_eq):
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
        logger.info("Analyse region (safe={}, check_for_eq={}, fixed_direction={})".format(safe, check_for_eq, self._fixed_direction))
        smt_successful = False
        smt_model = None
        assert self._fixed_direction is None or (safe and self._fixed_direction == "safe") or (not safe and self._fixed_direction == "bad")

        if isinstance(polygon, HyperRectangle):
            constraint = polygon.to_formula(self.parameters)
        else:
            raise RuntimeError("Unexpected type of region.")

        while not smt_successful:
            # check constraint with smt
            with self._getsolver(safe) as context:
                smt_context = context.smt_context
                fd = context.fd
                smt_context.assert_constraint(constraint)


                if not fd:
                    if check_for_eq:
                        smt_context.set_guard("?_equals", True)
                        smt_context.set_guard("?_safe", False)
                        smt_context.set_guard("?_bad", False)
                    else:
                        # Invert the safe flag to try and find a counter example
                        smt_context.set_guard("?_equals", False)
                        smt_context.set_guard("?_safe", not safe)
                        smt_context.set_guard("?_bad", safe)

                if not self._exact:
                    smt_context.set_guard("?_exact", False)


                start = time.time()
                checkresult = smt_context.check()
                duration = time.time() - start
                self._solver_timer += duration

                if check_for_eq:
                    if checkresult == Answer.unsat:
                        checkresult = RegionCheckResult.Homogenous
                    if checkresult == Answer.sat:
                        checkresult = RegionCheckResult.Inhomogenous
                    #TODO: Add benchmark output.

                else:
                    if checkresult == Answer.unsat:
                        checkresult = RegionCheckResult.Satisfied
                    if checkresult == Answer.sat:
                        checkresult = RegionCheckResult.CounterExample
                    self.benchmark_output.append((checkresult, duration, polygon.size()))


                if checkresult not in [RegionCheckResult.Satisfied, RegionCheckResult.CounterExample, RegionCheckResult.Homogenous, RegionCheckResult.Inhomogenous]:
                    break
                else:
                    if checkresult in [RegionCheckResult.CounterExample, RegionCheckResult.Inhomogenous]:
                        smt_model = smt_context.get_model()
                    break

        logger.debug("Check result is %s", checkresult)
        if checkresult in [RegionCheckResult.Satisfied, RegionCheckResult.Homogenous]:
            return checkresult, None
        elif checkresult in [RegionCheckResult.CounterExample, RegionCheckResult.Inhomogenous] and not self.over_approximates():
            return checkresult, self._evaluate(smt_model) if smt_model else None
        else:
            # SMT failed completely
            return RegionCheckResult.Unknown, None
