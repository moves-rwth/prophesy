import itertools
from numpy import linspace
from prophesy.data.interval import BoundType

from prophesy import config
from prophesy.data.samples import SamplePoints
from prophesy.data.point import Point
from pycarl import Rational

class Sampler(object):
    """Base class for performing sampling of given set of points"""
    def __init__(self):
        pass

    def perform_uniform_sampling(self, variables, intervals, samples_per_dimension):
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

        assert len(variables) == len(intervals)

        # points evenly spaced over the interval, for each dimension
        ranges = []
        for i in intervals:
            minNum = i.left_bound() if i.left_bound_type() == BoundType.closed else i.left_bound() + config.INTERVAL_EPSILON
            maxNum = i.right_bound() if i.right_bound_type() == BoundType.closed else i.right_bound() - config.INTERVAL_EPSILON
            ranges.append(map(Rational, linspace(minNum, maxNum, samples_per_dimension)))
        # turned into grid via cartesian product
        all_points = itertools.product(*ranges)
        all_points = [Point(*coords) for coords in all_points]

        sample_points = SamplePoints(all_points, variables)

        return self.perform_sampling(sample_points)

    def perform_sampling(self, samplepoints):
        """Samples the given sample point and returns the result as a
        SampleDict.
        @param iterable of SamplePoint or SamplePoints
        @return SampleDict
        """
        raise NotImplementedError("Abstract sampling function called")
