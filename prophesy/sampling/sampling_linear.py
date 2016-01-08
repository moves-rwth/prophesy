import math
from sampling.sampling import SampleGenerator, filter_samples, split_samples,\
    weighed_interpolation
from shapely.geometry.point import Point


class LinearRefinement(SampleGenerator):
    """Based on an initial set of samples, refines the samples by means
    of linear interpolation to approximate the threshold"""
    def __init__(self, sampler, samples, threshold):
        super().__init__(sampler)
        self.samples = samples.copy()
        self.threshold = threshold
        self.first = True

    def _min_dist(self):
        """Max. distance between two points to be considered"""
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
            d = point.distance(Point(sample_pt))
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
            self.samples = filter_samples(self.samples, self.threshold)
        else:
            self.first = False

        if len(self.samples) == 0:
            raise StopIteration()

        (safe_samples, bad_samples) = split_samples(self.samples, self.threshold)
        delta = self._min_dist()
        new_points = []

        # Offset the weight a little to balance the sample types
        if len(safe_samples) < len(bad_samples):
            # Move towards larger value if more safe samples required
            fudge = 0.01
        else:
            fudge = -0.01

        for safe_pt, safe_v in safe_samples.items():
            safe_pt = Point(safe_pt)
            for bad_pt, bad_v in bad_samples.items():
                bad_pt = Point(bad_pt)
                dist = safe_pt.distance(bad_pt)
                if 0.06 < dist < delta:
                    point = weighed_interpolation(safe_pt, bad_pt, safe_v, bad_v, self.threshold, fudge)
                    if point is not None and not self._is_too_close(point):
                        new_points.append(list(point.coords)[0])

        if not new_points:
            raise StopIteration()

        new_samples = self.sampler.perform_sampling(new_points)
        self.samples.update(new_samples)
        return new_samples
