from prophesy.regions.region_generation import RegionGenerator
from prophesy.data.hyperrectangle import HyperRectangle


class _AnnotatedRegion:
    """
    Named tuple holding the region and additional information
    """
    def __init__(self, region, samples, well_defined = None, graph_preserving = None):
        self.region = region
        self.samples = samples
        self.graph_preserving = graph_preserving
        self.well_defined = well_defined


class HyperRectangleRegions(RegionGenerator):
    def __init__(self, samples, parameters, threshold, checker):
        super().__init__(samples, parameters, threshold, checker)

        self.regions = []
        # Number of consecutive recursive splits() maximum
        self.check_depth = 64

        # Setup initial region
        region = HyperRectangle(*self.parameters.get_variable_bounds())
        regionsamples = []

        for instantiation, value in samples:
            if not region.contains(instantiation.get_point(parameters)):
                continue
            safe = value >= self.threshold
            regionsamples.append((instantiation.get_point(parameters), safe))
        self.check_region(region, regionsamples)
        self._sort_regions_by_size()

    def _sort_regions_by_size(self, reverse=True):
        self.regions.sort(key=lambda x: x.region.size(), reverse=reverse)

    def plot_candidate(self):
        boxes = []
        for q in self.regions:
            boxes.append(q.poly)
        self.plot_results(poly_blue=boxes, display=False)

    def check_region(self, region, samples, depth=0):
        """Check if given region can be assumed safe or bad based on
        known samples. If samples are mixed, split the region and retry.
        Resulting regions are added to self.regions"""
        if depth == self.check_depth:
            assert False, "Too deep"
            self.regions.append(region)
            return

        if len(samples) <= 1:
            self.regions.append(_AnnotatedRegion(region, samples))
            return
        if all([sample[1] for sample in samples]):
            # All safe
            self.regions.append(_AnnotatedRegion(region, samples))
            return
        elif all([not sample[1] for sample in samples]):
            # All bad
            self.regions.append(_AnnotatedRegion(region, samples))
            return

        newelems = region.split_in_every_dimension()
        if newelems is None:
            return None
        for newregion in newelems:
            newsamples = []
            for pt, safe in samples:
                if not newregion.contains(pt):
                    continue
                newsamples.append((pt, safe))
            self.check_region(newregion, newsamples, depth + 1)

    def fail_region(self, constraint, safe):
        # Split region and try again
        regionelem = self.regions[0]
        newelems = regionelem.region.split_in_every_dimension()
        # Currently no need to check it,
        # failure ony applies for region that was already consistent
        self.regions = self.regions[1:]
        for newregion in newelems:
            newsamples = []
            for pt, safe in regionelem.samples:
                if not newregion.contains(pt):
                    continue
                newsamples.append((pt, safe))
            self.regions.insert(0, _AnnotatedRegion(newregion, newsamples))
        self._sort_regions_by_size()
        region = self.regions[0]
        return region.region, safe

    def reject_region(self, constraint, safe, sample):
        # New sample, add it to current region, and check it
        # Also remove failed region
        self.regions[0].samples.append((sample.get_instantiation_point(self.parameters), not safe))
        self.check_region(self.regions[0].region, self.regions[0].samples)
        self.regions = self.regions[1:]
        self._sort_regions_by_size()
        
    def refine_region(self, new_regions, safe):
        """
        If a constraint could not be checked, but we know that only a subconstraint has to be checked afterwards.
        """
        self.regions = self.regions[1:]
        for region in new_regions:
            self.regions.append(region)
        self._sort_regions_by_size()

    def accept_region(self, constraint, safe):
        # Done with the region
        self.regions = self.regions[1:]

    def next_region(self):
        if len(self.regions) == 0:
            return None

        region = self.regions[0]

        if len(region.samples) == 0:
            # Assume safe at first (rather arbitrary)
            return  region.region, True
        if all([sample[1] for sample in region.samples]):
            # All safe
            return  region.region, True
        elif all([not sample[1] for sample in region.samples]):
            # All bad
            return region.region, False

        assert False, "A mixed region was left in the region queue, wut"
