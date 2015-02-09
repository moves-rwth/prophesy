import itertools
from config import SAMPLING_DISTANCE
from shapely.geometry import Point
from numpy import linspace
import ast
from collections import OrderedDict

class Sampler(object):
    """Base class for performing sampling of given set of points"""
    def __init__(self):
        pass

    def perform_uniform_sampling(self, intervals, samples_per_dimension):
        assert samples_per_dimension > 1
        ranges = [linspace(i[0], i[1], samples_per_dimension) for i in intervals]
        all_points = itertools.product(*ranges)
        return self.perform_sampling(all_points)

    def perform_sampling(self, samplepoints):
        return NotImplementedError("Abstract samplingfunction called")

class SampleGenerator(object):
    """Class to refine a given set of samples"""
    def __init__(self, sampler):
        self.sampler = sampler

    def refine_samples(self):
        raise NotImplemented()

def read_samples_file(path):
    parameters = []
    samples = {}
    threshold = None
    safe_above = None
    with open(path, 'r') as f:
        lines = [l.strip() for l in f.readlines()]
        if len(lines) > 2:
            parameters = lines[0].split()
            threshold = float(lines[1])
            safe_above = ast.literal_eval(lines[2])
            for i, line in enumerate(lines[3:]):
                items = line.split()
                if len(items) - 1 != len(parameters):
                    raise RuntimeError("Invalid input on line " + str(i+2))
                samples[tuple(map(float, items[:-1]))] = float(items[-1])
            samples = OrderedDict(samples.items())
    return (parameters, threshold, safe_above, samples)

def write_samples_file(parameters, samples_dict, threshold, safe_above, path):
    with open(path, "w") as f:
        f.write(" ".join(parameters) + "\n")
        f.write("{}\n{}\n".format(threshold, safe_above))
        for k, v in samples_dict.items():
            f.write("\t".join([("%.4f" % (c)) for c in k ]) + "\t\t" + "%.4f" % (v) + "\n")

def split_samples(samples, threshold, safe_above_threshold = True):
    """
    returns (safe, bad)
    """
    below_threshold = dict([(k, v) for k, v in samples.items() if v < threshold])
    above_threshold = dict([(k, v) for k, v in samples.items() if v >= threshold])
    if safe_above_threshold:
        return (above_threshold, below_threshold)
    else:
        return (below_threshold, above_threshold)

def filter_samples(samples, threshold, distance = SAMPLING_DISTANCE):
    """Returns samples which are less than 'distance' away from the threshold"""
    return {pt : val for (pt, val) in samples.items() if abs(threshold - val) <= distance}

def weighed_interpolation(point1, point2, value1, value2, threshold, fudge=0.0):
    distance = abs(value1-value2)
    weight = abs(threshold-value1)/distance
    weight += fudge
    return Point((point2.x-point1.x)*weight+point1.x, (point2.y-point1.y)*weight+point1.y)



