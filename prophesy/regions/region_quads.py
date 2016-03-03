from regions.region_generation import RegionGenerator
from data.point import Point
from data.hyperrectangle import HyperRectangle


class QuadAndSamples:
    def __init__(self, quad, samples):
        self.quad = quad
        self.samples = samples

class ConstraintQuads(RegionGenerator):
    def __init__(self, samples, parameters, threshold, threshold_area, _smt2interface, _ratfunc):
        super().__init__(samples, parameters, threshold, threshold_area, _smt2interface, _ratfunc)

        self.quads = []
        # Number of consecutive recursive splits() maximum
        self.check_depth = 64

        # Setup initial quad
        quad = HyperRectangle(*self._intervals())
        quadsamples = []

        for pt, v in samples.items():
            pt = Point(pt)
            if not quad.is_inside(pt):
                continue
            safe = v >= self.threshold
            quadsamples.append((pt, safe))
        self.check_quad(quad, quadsamples)
        self._sort_quads_by_size()

    def _sort_quads_by_size(self, reverse=True):
        self.quads.sort(key=lambda x: x.quad.size(), reverse=True)

    def plot_candidate(self):
        boxes = []
        for q in self.quads:
            boxes.append(q.poly)
        self.plot_results(poly_blue=boxes, display=False)


    def check_quad(self, quad, samples, depth=0):
        """Check if given quad can be assumed safe or bad based on
        known samples. If samples are mixed, split the quad and retry.
        Resulting quads are added to self.quads"""
        if depth == self.check_depth:
            assert False, "Too deep"
            self.quads.append(quad)
            return

        if len(samples) <= 1:
            self.quads.append(QuadAndSamples(quad, samples))
            return
        if all([sample[1] for sample in samples]):
            # All safe
            self.quads.append(QuadAndSamples(quad, samples))
            return
        elif all([not sample[1] for sample in samples]):
            # All bad
            self.quads.append(QuadAndSamples(quad, samples))
            return

        print("split quad {0}".format(quad))

        newelems = quad.split_in_every_dimension()
        if newelems is None:
            return None
        for newquad in newelems:
            newsamples = []
            for pt, safe in samples:
                if not newquad.is_inside(pt):
                    continue
                newsamples.append((pt, safe))
            self.check_quad(newquad, newsamples, depth + 1)




    def fail_constraint(self, constraint, safe):
        # Split quad and try again
        quadelem = self.quads[0]
        newelems = quadelem.quad.split_in_every_dimension()
        # Currently no need to check it,
        # failure ony applies for quad that was already consistent
        self.quads = self.quads[1:]
        for newquad in newelems:
            newsamples = []
            for pt, safe in quadelem.samples:
                if not newquad.is_inside(pt):
                    continue
                newsamples.append((pt, safe))
            self.quads.insert(0, QuadAndSamples(newquad, newsamples))
        self._sort_quads_by_size()
        quad = self.quads[0]
        return quad.quad, safe

    def reject_constraint(self, constraint, safe, sample):
        # New sample, add it to current quad, and check it
        # Also remove failed quad
        self.quads[0].samples.append((Point(sample[0]), not safe))
        self.check_quad(self.quads[0].quad, self.quads[0].samples)
        self.quads = self.quads[1:]
        self._sort_quads_by_size()

    def accept_constraint(self, constraint, safe):
        # Done with the quad
        self.quads = self.quads[1:]

    def next_constraint(self):
        if len(self.quads) == 0:
            return None

        quad = self.quads[0]

        if len(quad.samples) == 0:
            # Assume safe at first (rather arbitrary)
            return  quad.quad, True
        if all([sample[1] for sample in quad.samples]):
            # All safe
            return  quad.quad, True
        elif all([not sample[1] for sample in quad.samples]):
            # All bad
            return quad.quad, False

        assert False, "A mixed quad was left in the quad queue, wut"
