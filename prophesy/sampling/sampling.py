import itertools
import math
from collections import OrderedDict

from shapely.geometry import Point
from numpy import linspace

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
        ranges = [linspace(i[0], i[1], samples_per_dimension) for i in intervals]
        # turned into grid via cartesian product
        all_points = itertools.product(*ranges)

        return self.perform_sampling(all_points)

    def perform_sampling(self, samplepoints):
        raise NotImplementedError("Abstract sampling function called")


class SampleGenerator(object):
    """Class to refine a given set of samples"""
    def __init__(self, sampler):
        self.sampler = sampler

    def refine_samples(self):
        raise NotImplemented()


def read_samples_file(path):
    """
    Reads sample files.

    The first line specifies the parameters (with an optional "Result") for the last column.
    The second line optionally specifies a threshold. This is important if we have binary samples,
    (for which we do not know the value, but just whether it is above or below the threshold).
    The remaining lines give the parameter values and the value. This value is either a number or
    "above" or "below".

    :param path:
    :return:
    """
    parameters = []
    samples = {}
    threshold = None
    with open(path, 'r') as f:
        lines = [l.strip() for l in f.readlines()]
        if len(lines) > 2:
            parameters = lines[0].split()
            if parameters[-1] == "Result":
                #TODO we thus disallow parameters with the name Result (see restrictions.md)
                parameters = parameters[:-1]
            start = 1
            #Ignore thresholds
            if lines[1].startswith("Threshold"):
                if len(lines[1].split()) != 2:
                    raise IOError("Invalid input on line 2")
                threshold = float(lines[1].split()[1])
                start += 1
            for i, line in enumerate(lines[start:]):
                items = line.split()
                if len(items) - 1 != len(parameters):
                    raise RuntimeError("Invalid input on line " + str(i + start))
                if(items[-1] == "below" or items[-1] == "above"):
                    samples[tuple(map(float, items[:-1]))] = items[-1]
                else:
                    samples[tuple(map(float, items[:-1]))] = float(items[-1])
            samples = OrderedDict(samples.items())
    return parameters, threshold, samples


def write_samples_file(parameters, samples_dict, path):
    with open(path, "w") as f:
        f.write(" ".join(parameters) + "\n")
        for k, v in samples_dict.items():
            f.write("\t".join([("%.4f" % c) for c in k]) + "\t\t" + "%.4f" % v + "\n")


def split_samples(samples, threshold):
    """returns (>=, <)"""
    above_threshold = dict([(k, v) for k, v in samples.items() if v >= threshold])
    below_threshold = dict([(k, v) for k, v in samples.items() if v < threshold])
    return above_threshold, below_threshold

def filter_samples(samples, threshold, distance=config.DISTANCE):
    """Returns samples which are less than (or equal) `distance` away
       from the threshold"""
    return {pt: val for pt, val in samples.items() if abs(threshold - val) <= distance}


def weighed_interpolation(point1, point2, value1, value2, threshold, fudge=0.0):
    # TODO: A short docstring explaining what exactly this does would be nice
    distance = abs(value1 - value2)
    if distance < 0.00001:
        return None

    weight = abs(threshold - value1) / distance
    dx = point2.x - point1.x
    dy = point2.y - point1.y

    offset = abs(fudge) / math.sqrt(dx*dx + dy*dy)

    # Positive fudge moves towards larger value
    if (value1 > value2) == (fudge > 0):
        offset *= -1

    weight += offset

    return Point(dx*weight + point1.x, dy*weight + point1.y)



