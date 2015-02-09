import math
import numpy
import itertools
from config import SAMPLING_DISTANCE
from collections import OrderedDict
from shapely.geometry import Point
from sympy.core.numbers import Rational
from numpy import linspace
from constraints.voronoi import computeDelaunayTriangulation
from shapely.geometry.linestring import LineString
from shapely.geometry.multilinestring import MultiLineString
import ast

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

def get_evaluation(point, parameters):
    # returns list as evaluation for parameters according to point coordinates
    return {x:y for x,y in zip(parameters, point)}

class Sampling(object):
    def __init__(self):
        pass

    def perform_uniform_sampling(self, intervals, samples_per_dimension):
        assert samples_per_dimension > 1
        ranges = [linspace(i[0], i[1], samples_per_dimension) for i in intervals]
        all_points = itertools.product(*ranges)
        return self.perform_sampling(all_points)

    def perform_sampling(self, samplepoints):
        return NotImplementedError("Abstract samplingfunction called")

class McSampling(Sampling):
    def __init__(self, tool, prism_file, pctl_file):
        super().__init__()

        self.tool = tool
        self.prism_file = prism_file
        self.pctl_file = pctl_file
    
    def perform_uniform_sampling(self, intervals, samples_per_dimension):
        assert samples_per_dimension > 1
        ranges = [range.create_range_from_interval(interval, samples_per_dimension) for interval in intervals]
        samples = self.tool.uniform_sample_pctl_formula(self, self.prism_file, self.pctl_file, ranges)
        return OrderedDict(samples.items())

    def perform_sampling(self, samplepoints):
        samples = self.tool.sample_pctl_formula(self.prism_file, self.pctl_file, samplepoints)
        return OrderedDict(samples.items())

# Sampling for rational function
class RatFuncSampling(Sampling):
    def __init__(self, ratfunc, parameters, rational=False):
        super().__init__()

        self.parameters = parameters
        self.ratfunc = ratfunc
        self.rational = rational

    def perform_sampling(self, samplepoints):
        samples = {}
        for pt in samplepoints:
            if self.rational:
                samples[pt] = self.ratfunc.eval({x:Rational(y) for x,y in zip(self.parameters, pt)}).evalf()
            else:
                samples[pt] = self.ratfunc.eval({x:y for x,y in zip(self.parameters, pt)}).evalf()
        return OrderedDict(samples.items())

def split_samples(samples, threshold, greaterEqualSafe = True):
    """
    returns (safe, bad)
    """
    below_threshold = dict([(k, v) for k, v in samples.items() if v < threshold])
    above_threshold = dict([(k, v) for k, v in samples.items() if v >= threshold])
    if greaterEqualSafe:
        return (above_threshold, below_threshold)
    else:
        return (below_threshold, above_threshold)

def filter_sampling(samples, threshold):
    return {pt : val for (pt, val) in samples.items() if abs(threshold - val) <= SAMPLING_DISTANCE}

def near_sampling(samples, threshold, rectangles, limit = 0.1, added_dist = 0.05):
    pass

def refine_sampling(samples, threshold, sampling_interface, greaterEqualSafe = True, use_filter = False):
    """Given the current samples and threshold, generates a new set of samples to approximate
    the threshold function.
    If use_filter is True, samples that are too far from the threshold are ignored
    Returns an empty dictionary if no further refinement is possible"""
    samples = samples.copy()
    if use_filter:
        samples = filter_sampling(samples, threshold)
    (safe_samples, bad_samples) = split_samples(samples, threshold, greaterEqualSafe)
    samplenr = math.sqrt(len(samples))
    if samplenr <= 1:
        return {}
    bd = 0.1
    epsilon = (1 - 2 * bd) / (samplenr - 1)
    delta = math.sqrt(2 * (epsilon * epsilon) + epsilon / 2)
    skipCount = 0
    new_points = []
    for safe_pt, safe_v in safe_samples.items():
        for bad_pt, bad_v in bad_samples.items():
            safe_pt = Point(safe_pt)
            bad_pt = Point(bad_pt)
            # print(totalCount/prod)
            dist = safe_pt.distance(bad_pt)
            # print("safe_pt: {0}".format(safe_pt))
            # print("bad_pt: {0}".format(bad_pt))
            # print("distance: {0}".format( dist))
            if dist < delta and dist > 0.06:
                # constructCount = constructCount + 1
                # if constructCount % 10  == 0:
                    # print("constructCount {0}".format(constructCount))
                    
                # Calculate point approximately at the threshold assuming linear
                # function between safe and bad
                dist_to_safe = abs(safe_v - threshold)
                dist_to_bad = abs(threshold - bad_v)

                safe_weight = (dist_to_safe + 0.2) / (dist_to_safe + dist_to_bad + 0.4)
                bad_weight = (dist_to_bad + 0.2) / (dist_to_safe + dist_to_bad + 0.4)
                # print("safe_weight: {0}".format(safe_weight))
                # print("bad_weight: {0}".format(bad_weight))
                assert(abs(safe_weight + bad_weight - 1) < 0.05)

                point = Point(safe_weight * safe_pt.x + bad_weight * bad_pt.x, safe_weight * safe_pt.y + bad_weight * bad_pt.y)
                
                distance = abs(safe_v - bad_v)
                w1 = abs(safe_v - threshold)/distance
                # Offset the weight a little to balance the sample types
                if len(safe_samples) < len(bad_samples):
                    w1 -= 0.1
                else:
                    w1 += 0.1
                point = Point((bad_pt.x-safe_pt.x)*w1+safe_pt.x, (bad_pt.y-safe_pt.y)*w1+safe_pt.y)
                
                
                # Check if p is not too close to any other existing sample point
                skip = False
                i = 0
                for sample_pt in samples.keys():
                    d = point.distance(Point(sample_pt))
                    if d < 0.01:
                        #skip = True
                        skipCount += 1
                        break
                    elif d < 0.05:
                        i = i + 1
                        if i > 2:
                            #skip = True
                            skipCount += 1
                            break

                if not skip:
                    new_points.append(list(point.coords)[0])
    return sampling_interface.perform_sampling(new_points)

def weighed_interpolation(point1, point2, threshold, fudge=0.0):
    distance = abs(point1.z-point2.z)
    w1 = abs(threshold-point2.z)/distance
    w1 += fudge
    return Point((point2.x-point1.x)*w1+point1.x, (point2.y-point1.y)*w1+point1.y)

class SampleRefinement(object):
    def __init__(self, samples):
        self.samples = samples.copy()

    def refine_samples(self):
        raise NotImplemented()

class LinearRefinement(SampleRefinement):
    def __init__(self, samples):
        super().__init__(samples)

class DelaunayRefinement(SampleRefinement):
    def __init__(self, samples):
        super().__init__(samples)


class DelaunaySampling(object):
    @staticmethod
    def calcDelaunay(samples, threshold):
        """perform Delaunay triangulation of sample points. Limit the resulting triangles to those
        that contain both a safe and bad point"""
        points = []
        for pt, v in samples.items():
            # x,y as usual, z is value
            points.append(Point(pt[0], pt[1], v))
        dtriangles = computeDelaunayTriangulation(points)

        triangles = []
        for triangle in dtriangles:
            triangle = [points[i] for i in triangle]
            if all([p.z >= threshold for p in triangle]):
                continue
            if all([p.z < threshold for p in triangle]):
                continue

            # Triangle contains mixture of safe and bad points
            triangles.append(triangle)
        return triangles

    @staticmethod
    def calcApprox(triangles, threshold, samples):
        """Given set of triangle points, return the set of points
        that lie on an edge connecting a safe and bad point. The location
        is weighted by the value of the end points of each line"""
        # NOTE: A triangle can only have exactly two such points, or none
        # The resulting connecting line thus never splits
        lines = []
        safesamples = {k:v for k,v in samples.items() if v >= threshold}
        saf = len(safesamples)
        bad = len(samples) - saf
        for triangle in triangles:
            line = []
            points = triangle + [triangle[0]]
            pairs = zip(points[:-1], points[1:])
            for p1,p2 in pairs:
                if (p1.z >= threshold) == (p2.z >= threshold):
                    continue
                if saf > bad:
                    fudge = 0.1
                else:
                    fudge = -0.1
                line.append(weighed_interpolation(p1, p2, threshold, fudge))
            assert len(line) <= 2
            lines.append(line)
        return lines

    @staticmethod
    def calcSamples(samples, threshold, sampling_interface, distance = 0.05):
        triangles = DelaunaySampling.calcDelaunay(samples, threshold)
        lines = DelaunaySampling.calcApprox(triangles, threshold, samples)
        points = []
        for p1,p2 in lines:
            points.append(p1.coords[0])
            line = LineString([p1,p2])
            for d in numpy.arange(0, line.length, distance):
                pt = line.interpolate(d)
                points.append(pt.coords[0])
        return sampling_interface.perform_sampling(points)

    @staticmethod
    def calcLine(samples, threshold):
        """Return a new set of sample points as MultiLineString"""
        triangles = DelaunaySampling.calcDelaunay(samples, threshold)
        lines = DelaunaySampling.calcApprox(triangles, threshold, samples)
        lines = MultiLineString([LineString(line) for line in lines])
        return lines
