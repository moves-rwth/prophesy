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
        bd = 0.1
        epsilon = (1 - 2 * bd) / (samplenr - 1)
        delta = math.sqrt(2 * (epsilon * epsilon) + epsilon / 2)
        return delta

    def __iter__(self):
        self.first = True
        return self

    def __next__(self):
        if self.first:
            self.samples = filter_samples(self.samples, self.threshold)
            self.first = False

        if len(self.samples) == 0:
            raise StopIteration()

        (safe_samples, bad_samples) = split_samples(self.samples, self.threshold, True)
        delta = self._min_dist()
        new_points = []
        # Offset the weight a little to balance the sample types
        if len(safe_samples) < len(bad_samples):
            fudge = -0.1
        else:
            fudge = 0.1
        for safe_pt, safe_v in safe_samples.items():
            for bad_pt, bad_v in bad_samples.items():
                safe_pt = Point(safe_pt)
                bad_pt = Point(bad_pt)
                dist = safe_pt.distance(bad_pt)
                if dist < delta and dist > 0.06:
                    point = weighed_interpolation(safe_pt, bad_pt, safe_v, bad_v, self.threshold, fudge)

                    # Check if point is not too close to any other existing sample point
                    skip = False
                    i = 0
                    for sample_pt in self.samples.keys():
                        d = point.distance(Point(sample_pt))
                        if d < 0.01:
                            skip = True
                            break
                        elif d < 0.05:
                            i = i + 1
                            if i > 2:
                                skip = True
                                break

                    if not skip:
                        new_points.append(list(point.coords)[0])
        if len(new_points) == 0:
            raise StopIteration()

        new_samples = self.sampler.perform_sampling(new_points)
        self.samples.update(new_samples)
        return new_samples
