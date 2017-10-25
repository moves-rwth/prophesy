import itertools
from abc import abstractmethod
from numpy import linspace

from prophesy.data.interval import BoundType
from prophesy.config import configuration
from prophesy.data.samples import ParameterInstantiation
from prophesy.data.point import Point
from prophesy.adapter.pycarl import Rational


class Sampler:
    """
    Base class for performing sampling of given set of points
    """

    def __init__(self):
        pass

    def perform_uniform_sampling(self, parameters, samples_per_dimension):
        """
        Samples a uniform grid of points.

        Given a list of intervals (i.e., the first and last point;
        for each dimension, in order) and the number of samples per
        dimension, a uniformly-spaced grid of points (the cartesian
        product) is sampled.
        
        :param parameters: Parameters together with their region.
        :param samples_per_dimension: In how many points should the region be divided.
        """
        if samples_per_dimension < 1:
            raise RuntimeError("No. of samples per dimension must be >= 2")

        # points evenly spaced over the interval, for each dimension
        ranges = []
        for i in parameters.get_variable_bounds():
            minNum = i.left_bound() if i.left_bound_type() == BoundType.closed else i.left_bound() + configuration.get_sampling_epsilon()
            maxNum = i.right_bound() if i.right_bound_type() == BoundType.closed else i.right_bound() - configuration.get_sampling_epsilon()
            ranges.append(map(Rational, linspace(float(minNum), float(maxNum), samples_per_dimension)))
        # turned into grid via cartesian product
        all_points = itertools.product(*ranges)
        all_points = [Point(*coords) for coords in all_points]

        sample_points = [ParameterInstantiation.from_point(p, parameters) for p in all_points]

        return self.perform_sampling(sample_points)

    @abstractmethod
    def perform_sampling(self, samplepoints):
        """
        Given some parameter instantiations, perform sampling on these instantiations.
        
        :param samplepoints: An iterable yielding parameter instantiations
        :return: A collection with the results of these samples
        :rtype: InstantiationResultDict
        """
        raise NotImplementedError("Abstract sampling function called")
