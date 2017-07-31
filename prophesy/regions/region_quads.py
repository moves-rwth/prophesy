import logging
from prophesy.regions.region_generation import RegionGenerator
from prophesy.regions.welldefinedness import check_welldefinedness, WelldefinednessResult
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.smt.Z3cli_solver import Z3CliSolver

logger = logging.getLogger(__name__)


class _AnnotatedRegion:
    """
    Named tuple holding the region and additional information
    """
    def __init__(self, region, samples, safe=None, well_defined = WelldefinednessResult.Undecided, graph_preserving = None, closest_sample = None, closest_inverse_sample_distance = None):
        self.region = region
        self.samples = samples
        self.safe = safe
        self.graph_preserving = graph_preserving
        self.well_defined = well_defined
        self.closest_sample = closest_sample
        self.closest_inverse_sample_distance = closest_inverse_sample_distance
        self.empty_checks = 0 if len(samples) > 0 else 1


class HyperRectangleRegions(RegionGenerator):
    def __init__(self, samples, parameters, threshold, checker, wd_constraints, gp_constraints):
        super().__init__(samples, parameters, threshold, checker, wd_constraints, gp_constraints)

        self.regions = []
        self.parked_regions = []
        # Number of consecutive recursive splits() maximum
        self.check_depth = 5

        # Setup initial region
        region = HyperRectangle(*self.parameters.get_variable_bounds())
        regionsamples = []

        for instantiation, value in self.safe_samples:
            if not region.contains(instantiation.get_point(parameters)):
                continue
            regionsamples.append((instantiation.get_point(parameters), True))
        for instantiation, value in self.bad_samples:
            if not region.contains(instantiation.get_point(parameters)):
                continue
            regionsamples.append((instantiation.get_point(parameters), False))

        self.check_region(_AnnotatedRegion(region, regionsamples))
        self._sort_regions()

    def _sort_regions_by_size(self, reverse=True):
        self.regions.sort(key=lambda x: x.region.size(), reverse=reverse)

    def _sort_regions(self):
        self.regions.sort(key=lambda x: (x.well_defined != WelldefinednessResult.Illdefined, -x.region.size(), -x.closest_inverse_sample_distance if x.closest_inverse_sample_distance else 0))


    def plot_candidate(self):
        boxes = []
        boxes.append(self.regions[0].region)
        if self.regions[0].safe:
            self.plot_results(poly_blue_dotted=boxes, display=False)
        else:
            self.plot_results(poly_blue_crossed=boxes, display=False)

    def _compute_closest_inverse_sample(self, hypothesis_safe, region):
        if hypothesis_safe:
            inverse_samples = self.bad_samples
        else:
            inverse_samples = self.safe_samples

        if len(inverse_samples) == 0:
            return None
        else:
            center = region.center()
            dist = None
            for s in inverse_samples:
                new_dist = s[0].get_point(self.parameters).distance(center)
                if not dist or new_dist <= dist:
                    dist = new_dist
            return dist

    def _guess_hypothesis(self, region):
        logger.debug("Guess hypothesis for region %s", str(region))
        sublogger = logger.getChild("_guess_hypothesis")
        center = region.center()
        sublogger.debug("Center is at %s", center)
        dist = None
        for s in self.safe_samples:
            new_dist = s[0].get_point(self.parameters).distance(center)
            if not dist or new_dist <= dist:
                sublogger.debug("Currently closest safe sample: %s", s[0])
                dist = new_dist
        for s in self.bad_samples:
            new_dist = s[0].get_point(self.parameters).distance(center)
            if new_dist < dist:
                sublogger.debug("Currently closest bad sample  %s is closer than any safe sample", s[0])
                return False
        return True
        # TODO Consider close regions for this.

    def check_region(self, region, depth=0):
        """Check if given region can be assumed safe or bad based on
        known samples. If samples are mixed, split the region and retry.
        Resulting regions are added to self.regions"""
        if depth == self.check_depth:
            self.parked_regions.append(region)
            return

        if region.well_defined == WelldefinednessResult.Undecided:
            logger.info("Check well-definedness for the region")
            solver = Z3CliSolver()
            solver.run()
            wd_res = check_welldefinedness(solver, self.parameters, region.region, self.gp_constraints + self.wd_constraints)
            solver.stop()
            if wd_res == WelldefinednessResult.Illdefined:
                region.well_defined = WelldefinednessResult.Illdefined
                self.regions.append(region)
                return
            if wd_res == WelldefinednessResult.Welldefined:
                region.well_defined = WelldefinednessResult.Welldefined

        if region.well_defined == WelldefinednessResult.Welldefined:
            mixed = True
            hypothesis_safe = True
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
        newelems = region.region.split_in_every_dimension()
        if newelems is None:
            return None
        for newregion in newelems:
            newsamples = []
            for pt, safe in region.samples:
                if not newregion.contains(pt):
                    continue
                newsamples.append((pt, safe))
            self.check_region(_AnnotatedRegion(newregion, newsamples, well_defined=region.well_defined), depth + 1)

    def fail_region(self, constraint, safe):
        # Split region and try again
        regionelem = self.regions[0]

        # failure ony applies for region that was already consistent
        self.regions = self.regions[1:]
        if regionelem.empty_checks == 1:
            dist = self._compute_closest_inverse_sample(not regionelem.safe, regionelem.region)
            self.regions.insert(0, _AnnotatedRegion(regionelem.region,regionelem.samples, not regionelem.safe,  well_defined=regionelem.well_defined, closest_inverse_sample_distance=dist))
            self.regions[0].empty_checks = 2
        else:
            newelems = regionelem.region.split_in_every_dimension()
            for newregion in newelems:
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
                self.regions.insert(0, _AnnotatedRegion(newregion, newsamples, hypothesis, well_defined=regionelem.well_defined, closest_inverse_sample_distance=dist))

        self._sort_regions()
        region = self.regions[0]
        return region.region, safe


    def reject_region(self, constraint, safe, sample):
        # New sample, add it to current region, and check it
        # Also remove failed region
        self.regions[0].samples.append((sample.get_instantiation_point(self.parameters), not safe))
        self.check_region(self.regions[0])
        self.regions = self.regions[1:]
        self._sort_regions()
        
    def refine_region(self, new_regions, safe):
        """
        If a constraint could not be checked, but we know that only a subconstraint has to be checked afterwards.
        """
        self.regions = self.regions[1:]
        for region in new_regions:
            self.regions.append(region)
        self._sort_regions()

    def accept_region(self):
        # Done with the region
        self.regions = self.regions[1:]

    def ignore_region(self):
        # Skip region
        self.regions = self.regions[1:]

    def next_region(self):
        if len(self.regions) == 0:
            return None

        region = self.regions[0]
        assert region.well_defined != WelldefinednessResult.Undecided
        return region.region, region.well_defined, region.safe

