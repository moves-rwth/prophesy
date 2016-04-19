from collections import OrderedDict

class SamplePoint(dict):
    """Simple dictionary mapping a pycarl.Variable to pycarl.Rational.
    """
    pass

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

    def filter(self, threshold, distance=None):
        """Returns samples which are less than (or equal) `distance` away from
        the threshold. If distance is None, threshold is a function to apply
        as a filter.
        @param samples SampleDict
        @param threshold pycarl.Rational, or callable to filter values
        @param distance pycarl.Rational
        """
        if distance is None:
            return SampleDict([(k, v) for k, v in self.items() \
                if threshold(v)])
        else:
            return SampleDict([(k, v) for k, v in self.items() \
                if abs(threshold - v) <= threshold])

def split_samples(samples, threshold):
    return samples.split(threshold)

def filter_samples(samples, threshold, distance=None):
    return samples.filter(threshold, distance)
