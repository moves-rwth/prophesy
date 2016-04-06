import math

def _sqrt_approx(i):
    """
    :param i: a positive number
    :return: the approximate square root of i
    """
    #TODO this might be much closer than necessary here.
    return math.sqrt(i)
    #TODO if i is a rational number for which the sqrt might be not a rat. number, then use some approx.

class Point:
    """
    A n-dimensional point class.
    """
    def __init__(self, *args):
        self.coordinates = tuple(*args)

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

    def __repr__(self):
        return str(self)
