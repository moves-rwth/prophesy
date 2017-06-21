import math
import logging

from prophesy.sampling.sample_generator import SampleGenerator
from prophesy.data.samples import weighed_interpolation,  ParameterInstantiations

logger = logging.getLogger(__name__)


class LinearRefinement(SampleGenerator):
    """Based on an initial set of samples, refines the samples by means
    of linear interpolation to approximate the threshold"""
    def __init__(self, sampler, parameters, samples, threshold):
        super().__init__(sampler, parameters, samples)
        self.threshold = threshold

        self.first = True

    def __iter__(self):
        self.first = True
        return self

    def __next__(self):
        logger.debug("Compute new points to sample.")
        if not self.first:
            # TODO: what should the distance be?
            self.samples = self.samples.filter(lambda value: abs(value - self.threshold) * 800 > 1)
        else:
            self.first = False

        if len(self.samples) == 0:
            raise StopIteration()

        (safe_samples, bad_samples) = self.samples.split(self.threshold)
        new_points = self._compute_points(safe_samples, bad_samples)

        if not new_points:
            raise StopIteration()

        logger.info("%s new points computed. Now sample: ", len(new_points))
        new_samples = self.sampler.perform_sampling(new_points)
        logger.debug("Done sampling.")
        self.samples.update(new_samples)
        return new_samples

    def _min_dist(self):
        """Minimal distance between two points in order to be considered"""
        # depends on the number of samples
        samplenr = math.sqrt(len(self.samples))
        if samplenr <= 1:
            return 0
        # TODO: Looks a bit like voodoo.
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

    def _compute_points(self, safe_samples, bad_samples):
        delta = self._min_dist()
        new_points = ParameterInstantiations()
        new_points.parameters = self.parameters

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
        return new_points
