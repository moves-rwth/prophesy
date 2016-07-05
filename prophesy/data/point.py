import math
from pycarl import Rational

def _sqrt_approx(i):
    """
    :param i: a positive number
    :return: the approximate square root of i
    """
    orig_type = type(i)
    if not isinstance(i, (int, float)):
        # if i is a rational number for which the sqrt might be not a
        # ratonal number, then use some approx.
        i = float(i)

    #TODO this might be much closer than necessary here.
    float_sqrt = math.sqrt(i)
    return orig_type(float_sqrt)

class Point:
    """
    A n-dimensional point class.
    """
    def __init__(self, *args):
        """
        @param args Numerical values to represent the point. Any numerical type,
            recommended pycarl.Rational
        """
        assert len(args) > 1, "1D point, normally not needed"
        args = [a if isinstance(a, Rational) else Rational(a) for a in args]
        self.coordinates = tuple(args)
        #TODO: backwards compatibility for Delaunay
        self.x = self.coordinates[0]
        if len(self.coordinates) > 1:
            self.y = self.coordinates[1]
        if len(self.coordinates) > 2:
            self.z = self.coordinates[2]

    def distance(self, other):
        res = 0.0
        for i, j in zip(self.coordinates, other.coordinates):
            res = res + pow(i-j,2)
        return _sqrt_approx(res)

    def dimension(self):
        return len(self.coordinates)

    def projection(self, dims):
        return Point(*[self.coordinates[i] for i in dims])

    def __str__(self):
        return "(" + ",".join([str(i) for i in self.coordinates]) + ")"

    def __iter__(self):
        return iter(self.coordinates)

    def __len__(self):
        return len(self.coordinates)

    def __getitem__(self, key):
        return self.coordinates[key]

    def __eq__(self, other):
        return isinstance(other, Point) and self.coordinates == other.coordinates

    def __hash__(self):
        return hash(self.coordinates)

    def __repr__(self):
        return "Point({})".format(", ".join(map(repr,self.coordinates)))
