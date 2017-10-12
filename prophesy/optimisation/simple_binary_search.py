import logging
import prophesy.adapter.pycarl as pc
from prophesy.regions.region_checker import RegionCheckResult


from prophesy.data.hyperrectangle import HyperRectangle

logger = logging.getLogger(__name__)

class BinarySearchOptimisation():
    def __init__(self, smt_checker, problem_description, use_counterexample = True):
        self.smt_checker = smt_checker
        self.problem_description = problem_description
        self.use_counterexample = use_counterexample

    def search(self, requested_gap = pc.Rational("0.001"), max_iterations = 10, lower = pc.Rational(0), upper = pc.Rational(1)):
        region = HyperRectangle(*self.problem_description.parameters.get_variable_bounds())
        if self.smt_checker.supports_only_closed_regions():
            region = region.close()
        iterations = 0

        threshold = lower
        while upper == pc.inf:
            threshold = threshold * 2
            upper, lower = self._check_for_threshold(region,threshold,upper,lower)


        logger.info("Interval [{},{}] (size: {}) ".format(lower, upper, upper-lower))
        while requested_gap < upper - lower and max_iterations >= iterations:
            iterations = iterations + 1
            threshold = lower+(upper - lower)/2
            upper, lower = self._check_for_threshold(region,threshold,upper,lower)
            logger.info("Iteration: {}; Interval [{},{}] (size: {} ~= {}) ".format(iterations, lower, upper, upper - lower, float(upper-lower)))



    def _check_for_threshold(self, region, threshold, upper, lower):
        logger.info("For threshold {}".format(threshold))
        self.smt_checker.change_threshold(threshold)
        result, additional = self.smt_checker.analyse_region(region, False)
        if result == RegionCheckResult.Satisfied:
            upper = threshold
        elif result == RegionCheckResult.CounterExample:
            if self.use_counterexample:
                lower = max(additional.result, threshold)
            else:
                lower = threshold
        else:
            raise RuntimeError("Not supported result {}".format(result))
        return upper, lower
