import logging
import prophesy.adapter.pycarl as pc
from prophesy.regions.region_checker import RegionCheckResult


from prophesy.data.hyperrectangle import HyperRectangle

logger = logging.getLogger(__name__)

class BinarySearchOptimisation():
    def __init__(self, smt_checker, problem_description, use_counterexample=True):
        self.smt_checker = smt_checker
        self.problem_description = problem_description
        self.use_counterexample = use_counterexample
        for c in problem_description.welldefined_constraints:
            self.smt_checker._smt2interface.assert_constraint(c)

    def search(self, requested_gap = pc.Rational("0.001"), max_iterations = 10,  dir="max", realised = pc.Rational(0), bound = pc.Rational(1)):
        region = HyperRectangle(*self.problem_description.parameters.get_variable_bounds())
        if self.smt_checker.supports_only_closed_regions():
            region = region.close()
        iterations = 0
        assert dir in ["min", "max"]

        if dir == "max":
            threshold = realised
            while bound == pc.inf:
                threshold = threshold * 2
                bound, realised = self._check_for_threshold(region,threshold,bound,realised)

        if dir == "min":
            logger.info("Interval [{},{}] (size: {}) ".format(bound, realised, realised-bound))
        else:
            logger.info("Interval [{},{}] (size: {}) ".format(realised, bound, bound-realised))
        while requested_gap < abs(bound - realised) and max_iterations >= iterations:
            iterations = iterations + 1

            threshold = realised+abs(realised - bound)/2 if dir == "max" else realised-abs(realised - bound)/2
            bound, realised = self._check_for_threshold(region, threshold, dir == "max", bound, realised)
            if dir == "min":
                logger.info("Iteration: {}; Interval [{},{}] (size: {} ~= {}) ".format(iterations, bound, realised, realised - bound, float(realised-bound)))
            else:
                logger.info(
                    "Iteration: {}; Interval [{},{}] (size: {} ~= {}) ".format(iterations, realised, bound, bound - realised,
                                                                               float(bound - realised)))


    def _check_for_threshold(self, region, threshold, maximise, bound, realised):
        logger.info("For threshold {}".format(threshold))
        self.smt_checker.change_threshold(threshold)
        result, additional = self.smt_checker.analyse_region(region, not maximise)
        if result == RegionCheckResult.Satisfied:
            bound = threshold
        elif result == RegionCheckResult.CounterExample:
            if self.use_counterexample:
                realised = max(additional.result, threshold) if maximise else min(additional.result, threshold)
            else:
                realised = threshold
        else:
            raise RuntimeError("Not supported result {}".format(result))
        return bound, realised
