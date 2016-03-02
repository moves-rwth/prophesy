import math
from shapely.geometry import Point


class SampleGenerator(object):
    """Class to refine a given set of samples"""
    def __init__(self, sampler, intervals):
        self.sampler = sampler
        self.intervals = intervals

    def refine_samples(self):
        raise NotImplemented()


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
