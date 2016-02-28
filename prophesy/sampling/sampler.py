import itertools
from numpy import linspace
from data.interval import  Interval, BoundType

import config

class Sampler(object):
    """Base class for performing sampling of given set of points"""
    def __init__(self):
        pass

    def perform_uniform_sampling(self, intervals, samples_per_dimension):
        """Samples a uniform grid of points.

           Given a list of intervals (i.e., the first and last point;
           for each dimension, in order) and the number of samples per
           dimension, a uniformly-spaced grid of points (the cartesian
           product) is sampled."""
        if samples_per_dimension < 1:
            raise RuntimeError("No. of samples per dimension must be >= 2")

        # points evenly spaced over the interval, for each dimension
        ranges = []
        for i in intervals:
            minNum = i.left_bound() if i.left_bound_type() == BoundType.closed else i.left_bound() + config.INTERVAL_EPSILON
            maxNum = i.right_bound() if i.right_bound_type() == BoundType.closed else i.right_bound() - config.INTERVAL_EPSILON
            ranges.append(linspace(minNum, maxNum, samples_per_dimension))
        # turned into grid via cartesian product
        all_points = itertools.product(*ranges)

        return self.perform_sampling(all_points)

    def perform_sampling(self, samplepoints):
        raise NotImplementedError("Abstract sampling function called")
