import itertools
from numpy import linspace
from prophesy.data.interval import BoundType

from prophesy.config import configuration
from prophesy.data.samples import SamplePoints
from prophesy.data.point import Point
from pycarl import Rational

class Sampler(object):
    """Base class for performing sampling of given set of points"""
    def __init__(self):
        pass

    def perform_uniform_sampling(self, variables_and_intervals, samples_per_dimension):
        """Samples a uniform grid of points.

        Given a list of intervals (i.e., the first and last point;
        for each dimension, in order) and the number of samples per
        dimension, a uniformly-spaced grid of points (the cartesian
        product) is sampled.
        @param variables VariableOrder
        @param iterable of Interval
        @param samples_per_dimension int
        """
        if samples_per_dimension < 1:
            raise RuntimeError("No. of samples per dimension must be >= 2")



        # points evenly spaced over the interval, for each dimension
        ranges = []
        for i in variables_and_intervals[1]:
            minNum = i.left_bound() if i.left_bound_type() == BoundType.closed else i.left_bound() + configuration.get_sampling_epsilon()
            maxNum = i.right_bound() if i.right_bound_type() == BoundType.closed else i.right_bound() - configuration.get_sampling_epsilon()
            ranges.append(map(Rational, linspace(float(minNum), float(maxNum), samples_per_dimension)))
        # turned into grid via cartesian product
        all_points = itertools.product(*ranges)
        all_points = [Point(*coords) for coords in all_points]

        sample_points = SamplePoints(all_points, variables_and_intervals[0])

        return self.perform_sampling(sample_points)

    def perform_sampling(self, samplepoints):
        """Samples the given sample point and returns the result as a
        SampleDict.
        @param iterable of SamplePoint or SamplePoints
        @return SampleDict
        """
        raise NotImplementedError("Abstract sampling function called")
