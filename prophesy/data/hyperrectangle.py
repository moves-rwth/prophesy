from prophesy.data.interval import Interval, BoundType
from prophesy.data.point import Point

class HyperRectangle(object):
    """
    Defines a hyper-rectangle, that is the Cartisean product of intervals,
    i.e. the n-dimensional variant of a box.
    """

    def __init__(self, *intervals):
        """
        :param intervals: An iterable with intervals for each dimension.
        :return:
        """
        self.intervals = tuple(intervals)

    @classmethod
    def from_extremal_points(cls, lowerpoint, upperpoint, boundtype ):
        """
        :param lowerpoint: A point corresponding to the lower boundary
        :param upperpoint:
        :return:
        """
        return cls.__init__([Interval(l,boundtype,r,boundtype) for l,r in zip(lowerpoint, upperpoint)])

    def __str__(self):
        return " x ".join([str(i) for i in self.intervals])

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        for i, j in zip(self.intervals, other.intervals):
            if not i == j: return False
        return True

    def dimension(self):
        return len(self.intervals)

    def empty(self):
        for interv in self.intervals:
            if interv.empty(): return True
        return False

    def vertices(self):
        result = []
        for i in range(0,pow(2,self.dimension()), 1):
            num_bits = self.dimension()
            bits = [(i >> bit) & 1 for bit in range(num_bits - 1, -1, -1)]
            result.append(Point([(self.intervals[i].left_bound() if x == 0 else self.intervals[i].right_bound()) for i,x in zip(range(0, self.dimension()), bits)]))
        return result

    #def vertices_and_inward_dir(self):

    def split_in_every_dimension(self):
        """
        Splits the hyperrectangle in every dimension
        :return: The 2^n many hyperrectangles obtained by the split
        """
        result = []
        splitted_intervals =  [tuple(interv.split()) for interv in self.intervals]
        for i in range(0,pow(2,self.dimension()), 1):
            num_bits = self.dimension()
            bits = [(i >> bit) & 1 for bit in range(num_bits - 1, -1, -1)]
            result.append(HyperRectangle([splitted_intervals[i][x] for i,x in zip(range(0, self.dimension()), bits)]))
        return result

    def size(self):
        """
        :return: The size of the hyperrectangle
        """
        s = 1
        for interv in self.intervals:
            s = s * interv.width()
        return s

    def is_inside(self, point):
        """
        :param point: An iterable over the coordinates of the point
        :return: True if inside, False otherwise
        """
        for p, interv  in zip(point, self.intervals):
            if not interv.contains(p): return False
        return True

    def intersect(self, other):
        """
        Computes the intersection
        :return:
        """
        return HyperRectangle([i1.intersect(i2) for i1, i2 in zip(self.intervals, other.intervals)])









