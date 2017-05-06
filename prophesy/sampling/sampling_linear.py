import math
from prophesy.sampling.sample_generator import SampleGenerator
from prophesy.data.samples import weighed_interpolation, ParameterInstantiation, ParameterInstantiations

class LinearRefinement(SampleGenerator):
    """Based on an initial set of samples, refines the samples by means
    of linear interpolation to approximate the threshold"""
    def __init__(self, sampler, parameters, samples, threshold):
        super().__init__(sampler, parameters.get_variables(), samples)
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

    def _is_too_close(self, p):
        """Check whether parameter instantiation p is too close to any other existing
        sample point."""
        i = 0
        for sample_pt in self.samples.instantiations():
            d = p.numerical_distance(sample_pt)
            if 100 * d < 1:
                return True
            elif 20 * d < 1:
                i = i + 1
                if i > len(p) - 1:
                    return True
        return False

    def __iter__(self):
        self.first = True
        return self

    def __next__(self):
        if not self.first:
            # TODO: what should the distance be?
            self.samples = self.samples.filter(lambda value: abs(value - self.threshold) * 800 > 1)
        else:
            self.first = False

        if len(self.samples) == 0:
            raise StopIteration()

        (safe_samples, bad_samples) = self.samples.split(self.threshold)
        delta = self._min_dist()
        new_points = ParameterInstantiations()

        # Offset the weight a little to balance the sample types
        if len(safe_samples) < len(bad_samples):
            # Move towards larger value if more safe samples required
            fudge = 0.01
        else:
            fudge = -0.01

        for safe_sample in safe_samples.instantiation_results():
            for bad_sample in bad_samples.instantiation_results():
                dist = safe_sample.instantiation.numerical_distance(bad_sample.instantiation)
                if 0.06 < dist < delta:
                    point = weighed_interpolation(safe_sample, bad_sample, self.threshold, fudge)
                    if point is not None and not self._is_too_close(point):
                        new_points.append(point)

        if not new_points:
            raise StopIteration()

        new_samples = self.sampler.perform_sampling(new_points)

        self.samples.update(new_samples)
        return new_samples
