import math
from prophesy.sampling.sample_generator import SampleGenerator
from prophesy.data.samples import weighed_interpolation, SamplePoints
from prophesy.data.point import Point

class LinearRefinement(SampleGenerator):
    """Based on an initial set of samples, refines the samples by means
    of linear interpolation to approximate the threshold"""
    def __init__(self, sampler, variables, samples, threshold):
        super().__init__(sampler, variables, samples)
        self.threshold = threshold

        self.first = True

    def _min_dist(self):
        """Max. distance between two points to be considered"""
        #TODO: What is going on here, hrmmm
        samplenr = math.sqrt(len(self.samples))
        if samplenr <= 1:
            return 0
        bd = 0.1
        epsilon = (1 - 2 * bd) / (samplenr - 1)
        delta = math.sqrt(2 * (epsilon * epsilon) + epsilon / 2)
        return delta

    def _is_too_close(self, point):
        """Check whether point is too close to any other existing
        sample point."""
        i = 0
        for sample_pt in self.samples.keys():
            d = point.distance(sample_pt)
            if d < 0.01:
                return True
            elif d < 0.05:
                i = i + 1
                if i > 2:
                    return True
        return False

    def __iter__(self):
        self.first = True
        return self

    def __next__(self):
        if not self.first:
            # TODO: what should the distance be?
            self.samples = self.samples.filter(lambda value: abs(value - self.threshold) > 0.00125)
        else:
            self.first = False

        if len(self.samples) == 0:
            raise StopIteration()

        (safe_samples, bad_samples) = self.samples.split(self.threshold)
        delta = self._min_dist()
        new_points = []

        # Offset the weight a little to balance the sample types
        if len(safe_samples) < len(bad_samples):
            # Move towards larger value if more safe samples required
            fudge = 0.01
        else:
            fudge = -0.01

        for safe_sample in safe_samples.samples():
            for bad_sample in bad_samples.samples():
                dist = safe_sample.pt.distance(bad_sample.pt)
                if 0.06 < dist < delta:
                    point = weighed_interpolation(safe_sample, bad_sample, self.threshold, fudge)
                    if point is not None and not self._is_too_close(point):
                        new_points.append(point)

        if not new_points:
            raise StopIteration()

        sample_points = SamplePoints(new_points, self.variables)

        new_samples = self.sampler.perform_sampling(sample_points)

        self.samples.update(new_samples)
        return new_samples
