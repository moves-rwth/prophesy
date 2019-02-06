import logging
import time
from prophesy.regions.region_checker import RegionChecker, RegionCheckResult
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.data.interval import BoundType
from prophesy.data.samples import ParameterInstantiation
from prophesy.data.point import Point
import prophesy.adapter.pycarl as pc

logger = logging.getLogger(__name__)

class MonoRegionChecker(RegionChecker):
    def __init__(self, backend):
        """
        Constructor.
        :param backend: 
        :type backend: ParametricModelChecker
        :param parameters: 
        """
        super().__init__()
        self._checker = backend
        self._parameters = None
        self.threshold = None
        self.fixed_threshold = True
        self.rounds = 0

    def initialize(self, problem_description, constants=None, fixed_threshold=True):
        self.fixed_threshold = fixed_threshold
        if not self.fixed_threshold:
            raise NotImplementedError("Variable thresholds are not supported at this time")
        if not problem_description.model:
            raise ValueError("Mono/Sampling Checker requires the model to be present")
        if not problem_description.property:
            raise ValueError("Mono/Sampling Checker requires the property to be present")
        self._parameters = problem_description.parameters
        self._checker.set_pctl_formula(problem_description.property)
        self.threshold = problem_description.threshold

    def supports_only_closed_regions(self):
        return False

    def _getminanchor(self, growing, hyperrectangle):
        return hyperrectangle.get_vertex(growing)

    def _getmaxanchor(self, growing, hyperrectangle):
        return hyperrectangle.get_vertex([(not grow) for grow in growing])

    def _evaluate(self, point):
        logger.debug("Evaluating at {}".format(point))
        results = self._checker.perform_sampling([ParameterInstantiation.from_point(point, self._parameters)], True)
        return list(results.values())[0]

    def _shrink(self, hyperrectangle, safe, growing):
        def _iterate_above(min, max):
            i = 0
            result = None
            center = (min + max) * pc.Rational(0.5)
            while i < 5:
                value = self._evaluate(center)
                if value > self.threshold:
                    result = center
                    center = (center + min) * pc.Rational(0.5)
                    i += 1
                else:
                    center = (center + max) * pc.Rational(0.5)
                    i += 2
            return result

        def _iterate_below(min, max):
            i = 0
            result = None
            center = (min + max) * pc.Rational(0.5)
            while i < 5:
                value = self._evaluate(center)
                if value < self.threshold:
                    result = center
                    center = (center + max) * pc.Rational(0.5)
                    i += 1
                else:
                    center = (center + min) * pc.Rational(0.5)
                    i += 2
            return result

        minanchor = self._getminanchor(growing, hyperrectangle)
        maxanchor = self._getmaxanchor(growing, hyperrectangle)

        if self._evaluate(minanchor) > self.threshold:
            return RegionCheckResult.Splitted, ([hyperrectangle],[],[])
        if self._evaluate(maxanchor) < self.threshold:
            return RegionCheckResult.Splitted, ([],[hyperrectangle],[])

        safe_regions = []  # [above_threshold_region]
        bad_regions = []  # [below_threshold_region]

        # First, shrink horizontally:
        max_on_min_projected = Point(minanchor[0], maxanchor[1])
        res = _iterate_above(minanchor, max_on_min_projected)
        if res is not None:
            reg = HyperRectangle.from_extremal_points(res, maxanchor, boundtype=BoundType.closed)
            assert reg.size() > 0
            logger.debug("Add safe region: {} (type 1)".format(reg))
            safe_regions.append(reg)
            maxanchor = Point(maxanchor[0], res[1])

        min_on_max_projected = Point(maxanchor[0], minanchor[1])
        res = _iterate_above(minanchor, min_on_max_projected)
        if res is not None:
            reg = HyperRectangle.from_extremal_points(res, maxanchor, boundtype=BoundType.closed)
            assert reg.size() > 0
            logger.debug("Add safe region: {} (type 2)".format(reg))
            safe_regions.append(reg)
            maxanchor = Point(res[0], maxanchor[1])

        max_on_min_projected = Point(minanchor[0], maxanchor[1])
        res = _iterate_below(max_on_min_projected, maxanchor)
        if res is not None:
            reg = HyperRectangle.from_extremal_points(res, minanchor, boundtype=BoundType.closed)
            logger.debug("Add bad region: {} (type 1)".format(reg))
            assert reg.size() > 0
            bad_regions.append(reg)
            minanchor = Point(minanchor[0], res[1])

        min_on_max_projected = Point(maxanchor[0], minanchor[1])
        res = _iterate_below(max_on_min_projected, maxanchor)
        if res is not None:
            reg = HyperRectangle.from_extremal_points(res, minanchor, boundtype=BoundType.closed)
            logger.debug("Add bad region: {} (type 2)".format(reg))
            assert reg.size() > 0
            bad_regions.append(reg)
            minanchor = Point(res[0], minanchor[1])

        remaining = HyperRectangle.from_extremal_points(minanchor, maxanchor, boundtype=BoundType.closed)
        logger.debug("Safe area {}, Bad area {}, Remaining area {} ({} %)".format(float(sum([r.size() for r in safe_regions])), float(sum([r.size() for r in bad_regions])), float(remaining.size()), 100*float(remaining.size()/hyperrectangle.size())))

        return RegionCheckResult.Splitted, (safe_regions,bad_regions,[remaining])

    def _divide(self, hyperrectangle, safe, growing):

        minanchor = self._getminanchor(growing, hyperrectangle)
        maxanchor = self._getmaxanchor(growing, hyperrectangle)

        lower = minanchor
        upper = maxanchor
        lower_res = lower
        upper_res = upper

        iters = (16 if self.rounds < 3 else 6)
        for i in range(1, iters):
            logger.debug("Anchors are {} and {}".format(lower, upper))
            center = (lower + upper) * pc.Rational(0.5)
            logger.debug("Evaluating at {}".format(center))
            results = self._checker.perform_sampling([ParameterInstantiation.from_point(center, self._parameters)],
                                                     True)
            logger.debug("Result: {}".format(float(list(results.values())[0])))
            if list(results.values())[0] > self.threshold:
                upper = center
                upper_res = center
            else:
                lower = center
                lower_res = center

        below_threshold_region = HyperRectangle.from_extremal_points(minanchor, lower_res, boundtype=BoundType.open)
        above_threshold_region = HyperRectangle.from_extremal_points(maxanchor, upper_res, boundtype=BoundType.open)

        upper_on_min_projected = Point(minanchor[0], upper_res[1])
        max_on_min_projected = Point(minanchor[0], maxanchor[1])
        min_on_max_projected = Point(maxanchor[0], minanchor[1])
        lower_on_upper_projected = Point(lower_res[0], upper_res[1])

        mini_region = HyperRectangle.from_extremal_points(upper_on_min_projected, lower_res, boundtype=BoundType.closed)
        midi_region = HyperRectangle.from_extremal_points(max_on_min_projected, upper_res, boundtype=BoundType.closed)
        maxi_region = HyperRectangle.from_extremal_points(min_on_max_projected, lower_on_upper_projected, boundtype=BoundType.closed)


        safe_regions = [above_threshold_region]
        bad_regions = [below_threshold_region]
        # else:
        #     reject_regions = [above_threshold_region]
        #     accept_regions = [below_threshold_region]

        logger.debug("Area above: {}; Area below {}; Unknown area: {} ({} %)".format(float(above_threshold_region.size()), float(below_threshold_region.size()), float(mini_region.size() + midi_region.size() + maxi_region.size()),  float(100*(mini_region.size() + midi_region.size() + maxi_region.size())/hyperrectangle.size())))
        logger.debug("Result: lower: {} upper: {}".format(lower_res, upper_res))

        return RegionCheckResult.Splitted, (safe_regions, bad_regions, [mini_region, midi_region, maxi_region])

    def analyse_region(self, hyperrectangle, safe, check_for_eq):
        assert not check_for_eq
        if not len(self._parameters) == 2:
            raise NotImplementedError("Mono/Sampling Checker requires the model to have exactly two parameters")

        growing = [True, True]
        logger.warning("Unchecked assumption: Growing: {}".format(growing))

        start = time.time()
        done = False
        ratio = float(hyperrectangle.intervals[0].width()) / float(hyperrectangle.intervals[1].width())

        if self.rounds == 0 or ratio < 0.1 or ratio > 10:
            logger.debug("SHRINNK!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
            result, regions = self._shrink(hyperrectangle, safe, growing)
            if len(regions[0]) + len(regions[1]) > 0:
                done = True

        if not done:
            result, regions = self._divide(hyperrectangle, safe, growing)

        self.rounds += 1

        duration = time.time() - start

        logger.debug("Evaluation took  {} time".format(duration))



        #if isinstance(region, HyperRectangle):
        #    self.benchmark_output.append((regions_result, duration, region.size()))

        return result, regions
