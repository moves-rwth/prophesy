from collections import OrderedDict
from prophesy.data.point import Point
from pycarl import Rational

# Placeholder values for samples of which the exact value is not known,
# but can be considered safe (above) or unsafe (below)
SAMPLE_ABOVE = Rational(2)
SAMPLE_BELOW = Rational(-1)

# If a sample is requested that is out of bounds, result is invalid
SAMPLE_INVALID = None

class SamplePoint(dict):
    """Simple dictionary mapping a pycarl.Variable to pycarl.Rational.
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def get_point(self, variables):
        """Return the Point corresponding to this sample, given variable
        ordering provided as argument
        @param variables VariableOrder. Must correspond to variables of this
            sample point.
        """
        return Point(*[self[var] for var in variables])

    @classmethod
    def from_point(cls, pt, variables):
        """Construnct SamplePoint from Point and VariableOrder
        @param pt Point of pycarl.Rational
        @param variables VariableOrder
        """
        sp = cls()
        for (pt, var) in zip(pt, variables):
            sp[var] = pt

class SamplePoints(object):
    """Collection of SamplePoint. When iterated over, returns a SamplePoint,
    but internally stores things slightly more efficient
    """
    def __init__(self, points, variables):
        """
        @param points Iterable of Point
        @param variables VariableOrder
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
            tups = zip(self.variables, pt)
            yield SamplePoint({var:val for var, val in tups})

    def __item__(self, index):
        pass

    def __str__(self):
        return "SamplePoints({}, {})".format(self.points, self.variables)

    def __repr__(self):
        return "SamplePoints({!r}, {!r})".format(self.points, self.variables)

class Sample(object):
    """Class to represent a single sample. Maps a point (tuple of
    pycarl.Rational) to a value (pycarl.Rational).
    """

    def __init__(self, pt, val, variables=None):
        """
        @param pt data.Point. Order has to follow the canonical model order
        @param val pycarl.Rational
        @param variables VariableOrder (Optional)
        """
        self.pt = pt
        self.val = val
        self.variables = variables

    def distance(self, other):
        """Returns the distance (magnitute) between this sample and the other
        sample.
        @param other Sample
        @return pycarl.Rational
        """
        return self.pt.distance(other.pt)

    def reorder(self, variables):
        """returns a new Sample for which the coordinates are reordered
        according to the given variable order.
        @param variables VariableOrder, variables must match self.variables
        @return Sample
        """
        order = [self.variables.index(var) for var in variables]
        pt = Point(*[self.pt[index] for index in order])
        return Sample(pt, self.val, variables)

    @classmethod
    def from_sample_point(cls, sample_point, variables, value):
        """Create Sample out of given SamplePoint, variable ordering and value
        @param sample_point SamplePoint to indicate location
        @param variables VariableOrder. Must correspond to variables of the
            sample point.
        @value value pycarl.Rational, value of the Sample
        @return Sample
        """
        return cls(sample_point.get_point(variables), value, variables)

class SampleDict(OrderedDict):
    """Simple wrapper to maintain a dictionary of valuation -> sample. Ordering
    of the dictionary is based on order of sampling (and not valuation).
    Key is Point, Value is Rational
    """

    def __init__(self, variables=None):
        """
        @param variables, VariableOrder (Optional)
        """
        super().__init__()
        self.variables = variables

    def add_sample(self, sample):
        """
        @param sample Sample
        """
        self[sample.pt] = sample.val

    def split(self, threshold):
        """Split given samples into separated sample dictionaries, where the value
        either >= or < threshold.
        @param samples SampleDict
        @param threshold pycarl.Rational
        @return (SampleDict >=, SampleDict <)
        """
        above_threshold = SampleDict(self.variables)
        below_threshold = SampleDict(self.variables)
        for k, v in self.items():
            if v >= threshold:
                above_threshold[k] = v
            else:
                below_threshold[k] = v
        return above_threshold, below_threshold

    def filter(self, filter_func):
        """Returns samples for which filter_func returns true.
        @param samples SampleDict
        @param filter_func callable to filter values, return True to keep sample
        """
        filtered = SampleDict(self.variables)
        for k, v in self.items():
            if filter_func(v):
                filtered[k] = v
        return filtered

    def reorder(self, variables):
        """returns a new SampleDict for which the coordinates are reordered
        according to the given variable order.
        @param variables VariableOrder, variables must match self.variables
        @return SampleDict
        """
        order = [self.variables.index(var) for var in variables]
        sorted_dict = SampleDict(variables)
        for k, v in self.items():
            pt = Point(*[k[index] for index in order])
            sorted_dict[pt] = v
        return sorted_dict

    def copy(self):
        copy_dict = SampleDict(self.variables)
        for k, v in self.items():
            copy_dict[k] = v
        return copy_dict

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
