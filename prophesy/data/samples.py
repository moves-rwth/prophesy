from collections import OrderedDict
import math

class SamplePoint(dict):
    """Simple dictionary mapping a pycarl.Variable to pycarl.Rational.
    """

class SamplePoints(object):
    """Collection of SamplePoint. When iterated over, returns a SamplePoint,
    but internally stores things slightly more efficient
    """
    def __init__(self, points, variables):
        """
        @param points Iterable of tuples containing pycarl.Rational. Each tuple
        arity must match size of variables
        @param Ordered iterable of pycarl.Variable
        """
        self.points = points
        self.variables = variables

    def __len__(self):
        return len(self.points)

    def __getitem__(self, key):
        pt = self.points[key]
        tups = zip(pt, self.variables)
        return {var:val for var, val in tups}

    def __setitem__(self, key, value):
        self.points[key] = value

    def __reversed__(self):
        return reversed(self.points)

    def __iter__(self):
        for pt in self.points:
            assert len(pt) == len(self.variables), \
                "Sample point not defined for all variables"
            tups = zip(pt, self.variables)
            yield {var:val for var, val in tups}

    def __item__(self, index):
        pass

class Sample(object):
    """Class to represent a single sample. Maps a point (tuple of
    pycarl.Rational) to a value (pycarl.Rational).
    """

    def __init__(self, pt, val):
        """
        @param pt Tuple of pycarl.Rational
        @param val pycarl.Rational
        """
        self.pt = pt
        self.val = val

    def distance(self, other):
        """Returns the distance (magnitute) between this sample and the other
        sample.
        @param other Sample
        @return pycarl.Rational
        """
        deltas = tuple([pt2 - pt1 for (pt1, pt2) in zip(self.pt, other.pt)])
        return math.sqrt(float(sum([d*d for d in deltas])))

class SampleDict(OrderedDict):
    """Simple wrapper to maintain a dictionary of valuation -> sample. Ordering
    is based on order of sampling (and not valuation)
    Valuation is a dictionary {pycarl.Variable, pycarl.Rational}, sample
    is a pycarl.Rational
    """

    def split(self, threshold):
        """Split given samples into separated sample dictionaries, where the value
        either >= or < threshold.
        @param samples SampleDict
        @param threshold pycarl.Rational
        @return (SampleDict >=, SampleDict <)
        """
        above_threshold = SampleDict([(k, v) for k, v in self.items() \
            if v >= threshold])
        below_threshold = SampleDict([(k, v) for k, v in self.items() \
            if v < threshold])
        return above_threshold, below_threshold

    def filter(self, filter_func):
        """Returns samples for which filter_func returns true.
        @param samples SampleDict
        @param filter_func callable to filter values, return True to keep sample
        """
        return SampleDict([(k, v) for k, v in self.items() if filter_func(v)])

def split_samples(samples, threshold):
    """
    @see SampleDict.split
    """
    return samples.split(threshold)

def weighed_interpolation(sample1, sample2, threshold, fudge=0.0):
    """Interpolates between sample sample1 and sample2 to
    result in a point estimated close to the given treshold (by linear
    interpolation). Fudge allows to offset this point slightly either
    positively or negatively.
    @param sample1 Sample
    @param sample2 Sample
    @param threshold pycarl.Rational
    @param fudge float Percentage of distance betwen both samples to fudge
        around
    @return tuple of pycarl.Rational if interpolated point, or None if the
        values are too close
    """
    # If point values are too close, do not interpolate
    distance = abs(sample1.val - sample2.val)
    if distance < 0.00001:
        return None

    weight = abs(threshold - sample1.val) / distance

    deltas = tuple([pt2 - pt1 for (pt1, pt2) in zip(sample1.pt, sample2.pt)])

    magnitude = sample1.distance(sample2)
    offset = abs(fudge) / magnitude

    # Positive fudge moves towards larger value
    if (sample1.val > sample2.val) == (fudge > 0):
        offset *= -1

    weight += offset

    return tuple([d*weight + pt] for d, pt in zip(deltas, sample1.pt))
