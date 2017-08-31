import logging
import itertools

from prophesy.regions.region_generation import RegionGenerator
from prophesy.regions.welldefinedness import check_welldefinedness, WelldefinednessResult
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.data.interval import BoundType
from prophesy.data.point import Point
from prophesy.smt.Z3cli_solver import Z3CliSolver

logger = logging.getLogger(__name__)


class _AnnotatedRegion:
    """
    Named tuple holding the region and additional information.
    """

    def __init__(self, region, samples, safe=None, well_defined=WelldefinednessResult.Undecided,
                 graph_preserving=WelldefinednessResult.Undecided, closest_sample=None,
                 closest_inverse_sample_distance=None):
        self.region = region
        self.samples = samples
        self.safe = safe
        self.graph_preserving = graph_preserving
        self.well_defined = well_defined
        self.closest_sample = closest_sample
        self.closest_inverse_sample_distance = closest_inverse_sample_distance
        self.empty_checks = 0 if len(samples) > 0 else 1


class HyperRectangleRegions(RegionGenerator):
    """
    Region generation using hyperrectangles.
    """

    def __init__(self, samples, parameters, threshold, checker, wd_constraints, gp_constraints, split_uniformly=False):
        super().__init__(samples, parameters, threshold, checker, wd_constraints, gp_constraints)

        self.regions = []
        self.parked_regions = []
        self.accepted_regions_safe = []
        self.accepted_regions_unsafe = []
        # Number of maximal consecutive recursive splits.
        self.check_depth = 5
        if split_uniformly:
            self.split = HyperRectangleRegions.split_uniformly_in_every_dimension
        else:
            self.split = HyperRectangleRegions.split_by_growing_rectangles

        # Setup initial region
        region = HyperRectangle(*self.parameters.get_variable_bounds())
        if checker.supports_only_closed_regions():
            region = region.close()
        regionsamples = []

        # Add all samples to region
        for instantiation, value in self.safe_samples:
            if region.contains(instantiation.get_point(parameters)):
                regionsamples.append((instantiation.get_point(parameters), True))
        for instantiation, value in self.bad_samples:
            if region.contains(instantiation.get_point(parameters)):
                regionsamples.append((instantiation.get_point(parameters), False))

        # Check initial region
        self.check_region(_AnnotatedRegion(region, regionsamples))
        self._sort_regions()

    def _sort_regions_by_size(self, reverse=True):
        """
        Sort regions by size.
        :param reverse: Flag indicating if order should be reversed.
        """
        self.regions.sort(key=lambda x: x.region.size(), reverse=reverse)

    def _sort_regions(self):
        """
        Sort regions by size and closest inverse sample distance.
        """
        self.regions.sort(key=lambda x: (x.well_defined != WelldefinednessResult.Illdefined, -x.region.size(),
                                         -x.closest_inverse_sample_distance if x.closest_inverse_sample_distance else 0))

    def plot_candidate(self):
        boxes = [self.regions[0].region]
        if self.regions[0].safe:
            self.plot_results(poly_blue_dotted=boxes, display=False)
        else:
            self.plot_results(poly_blue_crossed=boxes, display=False)

    def _compute_closest_inverse_sample(self, hypothesis_safe, region):
        """
        Get sample clostest to the region center.
        :param hypothesis_safe: Flag iff the region is considered safe.
        :param region: Region.
        :return: Closest sample to region center or None if no sample was found.
        """
        if hypothesis_safe:
            inverse_samples = self.bad_samples
        else:
            inverse_samples = self.safe_samples

        if len(inverse_samples) == 0:
            return None
        else:
            center = region.center()
            dist = None
            for sample in inverse_samples:
                new_dist = sample[0].get_point(self.parameters).distance(center)
                if not dist or new_dist <= dist:
                    dist = new_dist
            return dist

    def _guess_hypothesis(self, region):
        """
        Get hypothesis for region according to closest sample.
        :param region: Region.
        :return: True iff the region hypothesis is safe.
        """
        logger.debug("Guess hypothesis for region {}".format(region))
        sublogger = logger.getChild("_guess_hypothesis")
        center = region.center()
        sublogger.debug("Center is at {}".format(center))
        dist = None
        for sample in self.safe_samples:
            new_dist = sample[0].get_point(self.parameters).distance(center)
            if not dist or new_dist <= dist:
                sublogger.debug("Currently closest safe sample: {}".format(sample[0]))
                dist = new_dist
        for sample in self.bad_samples:
            new_dist = sample[0].get_point(self.parameters).distance(center)
            if new_dist < dist:
                sublogger.debug("Currently closest bad sample {} is closer than any safe sample".format(sample[0]))
                return False
        return True
        # TODO Consider close regions for this.

    @staticmethod
    def split_by_growing_rectangles(region):
        """
        Split the region according to growing rectangles.
        :param region: Region.
        :return: New regions after splitting.
        """
        logger.debug("Split region {}".format(region.region))
        result = []

        # Get all anchor points
        bounds = [(interv.left_bound(), interv.right_bound()) for interv in region.region.intervals]
        anchor_points = [Point(*val) for val in itertools.product(*bounds)]

        best_candidate = None
        for anchor in anchor_points:
            for anchor2, safe_anchor in region.samples:
                rectangle = HyperRectangle.from_extremal_points(anchor, anchor2,
                                                                BoundType.closed)  # TODO handle open intervals
                assert rectangle is not None
                if best_candidate is not None and rectangle.size() <= best_candidate[0]:
                    # Larger candidate already known
                    continue

                # Check candidate
                valid = True
                for pt, safe in region.samples:
                    if rectangle.contains(pt) and safe != safe_anchor:
                        valid = False
                        break
                if valid:
                    # Found better candidate
                    best_candidate = (rectangle.size(), anchor, anchor2)

        assert best_candidate is not None

        logger.debug(
            "Candidate: {} for anchor {} and sample {}".format(best_candidate[0], best_candidate[1], best_candidate[2]))
        # Construct hyperrectangle for each anchor and the sample point
        for anchor in anchor_points:
            new_rectangle = HyperRectangle.from_extremal_points(anchor, best_candidate[2], BoundType.closed)
            result.append(new_rectangle)

        logger.debug("New regions:\n\t{}".format("\n\t".join([str(region) for region in result])))
        return result

    @staticmethod
    def split_uniformly_in_every_dimension(region):
        """
        Split the region uniformly in every region.
        :param region: Region.
        :return: New regions after splitting.
        """
        return region.region.split_in_every_dimension()

    def check_region(self, region, depth=0):
        """
        Check if the given region can be assumed safe or bad based on known samples.
        If samples are mixed, split the region and retry.
        Resulting regions are added to self.regions.
        :param region: Region.
        :param depth: Maximal depth for region refining.
        """
        if depth >= self.check_depth:
            self.parked_regions.append(region)
            return

        if self.checker.supports_only_closed_regions():
            region.region = region.region.close()

        # TODO check graph preserving seperately.
        if region.well_defined == WelldefinednessResult.Undecided:
            logger.info("Check well-definedness for the region")
            solver = Z3CliSolver()
            solver.run()
            wd_res = check_welldefinedness(solver, self.parameters, region.region,
                                           self.gp_constraints + self.wd_constraints)
            solver.stop()
            if wd_res == WelldefinednessResult.Illdefined:
                region.well_defined = WelldefinednessResult.Illdefined
                self.regions.append(region)
                return
            if wd_res == WelldefinednessResult.Welldefined:
                region.well_defined = WelldefinednessResult.Welldefined
                region.graph_preserving = WelldefinednessResult.Welldefined

        if region.well_defined == WelldefinednessResult.Welldefined:
            mixed = True
            if len(region.samples) == 1:
                hypothesis_safe = region.samples[0][1]
                mixed = False
            elif len(region.samples) == 0:
                hypothesis_safe = self._guess_hypothesis(region.region)
                mixed = False
            elif all([sample[1] for sample in region.samples]):
                # All safe
                hypothesis_safe = True
                mixed = False
            elif all([not sample[1] for sample in region.samples]):
                # All bad
                hypothesis_safe = False
                mixed = False

            if not mixed:
                dist = self._compute_closest_inverse_sample(hypothesis_safe, region.region)
                region.safe = hypothesis_safe
                region.closest_inverse_sample_distance = dist
                self.regions.append(region)
                return

        # Mixed region, split.
        # TODO better splits
        newelems = self.split(region)
        if newelems is None:
            return None
        for newregion in newelems:
            newsamples = []
            for pt, safe in region.samples:
                if newregion.contains(pt):
                    newsamples.append((pt, safe))
            self.check_region(_AnnotatedRegion(newregion, newsamples, well_defined=region.well_defined,
                                               graph_preserving=region.graph_preserving), depth + 1)

    def fail_region(self):
        # Split region and try again
        regionelem = self.regions[0]

        # failure ony applies for region that was already consistent
        self.regions = self.regions[1:]
        if regionelem.empty_checks == 1:
            dist = self._compute_closest_inverse_sample(not regionelem.safe, regionelem.region)
            self.regions.insert(0, _AnnotatedRegion(regionelem.region, regionelem.samples, not regionelem.safe,
                                                    well_defined=regionelem.well_defined,
                                                    graph_preserving=regionelem.graph_preserving,
                                                    closest_inverse_sample_distance=dist))
            self.regions[0].empty_checks = 2
        else:
            newelems = self.split(regionelem)
            for newregion in newelems:
                if self.checker.supports_only_closed_regions:
                    newregion = newregion.close()
                newsamples = []

                for pt, safe in regionelem.samples:
                    if not newregion.contains(pt):
                        continue
                    newsamples.append((pt, safe))
                if len(newsamples) == 0:
                    hypothesis = self._guess_hypothesis(newregion)
                else:
                    hypothesis = regionelem.safe

                dist = self._compute_closest_inverse_sample(hypothesis, newregion)
                self.regions.insert(0, _AnnotatedRegion(newregion, newsamples, hypothesis,
                                                        well_defined=regionelem.well_defined,
                                                        graph_preserving=regionelem.graph_preserving,
                                                        closest_inverse_sample_distance=dist))

        self._sort_regions()

    def reject_region(self, sample):
        # New sample, add it to current region
        self.regions[0].samples.append((sample.get_instantiation_point(self.parameters), not self.regions[0].safe))
        # Check region
        self.check_region(self.regions[0])
        # Also remove failed region
        self.regions = self.regions[1:]
        self._sort_regions()

    def refine_region(self, new_regions):
        """
        If a constraint could not be checked, but we know that only a subconstraint has to be checked afterwards.
        """
        self.regions = self.regions[1:]
        for region in new_regions:
            self.regions.append(region)
        self._sort_regions()

    def accept_region(self):
        # Done with the region
        if self.regions[0].safe:
            self.accepted_regions_safe.append(self.regions[0])
        else:
            self.accepted_regions_unsafe.append(self.regions[0])
        # Remove from all regions
        self.regions = self.regions[1:]

    def ignore_region(self):
        # Remove region
        self.regions = self.regions[1:]

    def next_region(self):
        if len(self.regions) == 0:
            return None

        region = self.regions[0]
        if self.checker.supports_only_closed_regions():
            while len(self.regions) > 0:
                regions_opposite = self.accepted_regions_unsafe if region.safe else self.accepted_regions_safe
                refuted = False
                for r in regions_opposite:
                    if r.region.non_empty_intersection(region.region):
                        self.fail_region()
                        region = self.regions[0]
                        refuted = True
                        break
                if not refuted:
                    break

        assert region.well_defined != WelldefinednessResult.Undecided
        return region.region, region.well_defined, region.safe
