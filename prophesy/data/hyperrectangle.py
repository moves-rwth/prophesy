from prophesy.data.interval import Interval
from prophesy.data.point import Point

import numpy as np

class HyperRectangle(object):
    """
    Defines a hyper-rectangle, that is the Cartisean product of intervals,
    i.e. the n-dimensional variant of a box.
    """

    def __init__(self, *intervals):
        """
        :param intervals: Multiple Intervals as arguments
        """
        self.intervals = tuple(intervals)

    @classmethod
    def from_extremal_points(cls, lowerpoint, upperpoint, boundtype ):
        """
        :param lowerpoint: A point corresponding to the lower boundary
        :param upperpoint: A point corresponding to the upper boundary
        :param boundtype: BoundType to use as bounds for the resulting
            HyperRectangle
        :return HyperRectangle
        """
        return cls.__init__(*[Interval(l,boundtype,r,boundtype) for l,r in zip(lowerpoint, upperpoint)])

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
            result.append(Point(*[(self.intervals[i].left_bound() if x == 0 else self.intervals[i].right_bound()) for i,x in zip(range(0, self.dimension()), bits)]))
        return result

    def np_vertices(self):
        verts = self.vertices()
        return np.array([np.array(list(map(float,v))) for v in verts])

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
            result.append(HyperRectangle(*[splitted_intervals[i][x] for i,x in zip(range(0, self.dimension()), bits)]))
        return result

    def size(self):
        """
        :return: The size of the hyperrectangle
        """
        s = 1
        for interv in self.intervals:
            s = s * interv.width()
        return s

    def contains(self, point):
        """
        :param point: A Point
        :return: True if inside, False otherwise
        """
        for p, interv in zip(point, self.intervals):
            if not interv.contains(p): return False
        return True

    def intersect(self, other):
        """
        Computes the intersection
        :return:
        """
        return HyperRectangle([i1.intersect(i2) for i1, i2 in zip(self.intervals, other.intervals)])

    def _setminus(self, other, dimension):
        assert len(self.intervals) > dimension and len(other.intervals) > dimension
        new_interval_list = self.intervals[dimension].setminus(other.intervals[dimension])
        hrect_list = []
        if len(new_interval_list) > 1:

            # left part
            changed_interval_list = list(self.intervals)
            changed_interval_list[dimension] = new_interval_list[0]
            hrect_list.append(HyperRectangle(*changed_interval_list))

            # right part
            changed_interval_list = list(self.intervals)
            changed_interval_list[dimension] = new_interval_list[1]
            hrect_list.append(HyperRectangle(*changed_interval_list))

            # middle part which is cut away
            middle_interval = Interval(new_interval_list[0].right_bound(), new_interval_list[0].right_bound_type(),
                                       new_interval_list[1].left_bound(), new_interval_list[1].left_bound_type())
            changed_interval_list = list(self.intervals)
            changed_interval_list[dimension] = middle_interval
            hrect_list.append(HyperRectangle(*changed_interval_list))

        else:
            # the cutted box
            changed_interval_list = list(self.intervals)
            changed_interval_list[dimension] = new_interval_list[0]
            hrect_list.append(HyperRectangle(*changed_interval_list))

            # the rest which have to be cutted recursively
            changed_interval_list = list(self.intervals)
            changed_interval_list[dimension] = other.intervals[dimension]
            hrect_list.append(HyperRectangle(*changed_interval_list))

        return hrect_list

    def setminus(self, other, dimension=0):
        """
        DOES NOT WORK
        TODO: erweitere implementierung auf mehr dimensionen
        :param other: the other HyperRectangle
        :param dimension: dimension where to start the operation
        :return: a list of HyperRectangles
        """
        assert len(other.intervals) == len(self.intervals)
        hrect_list = []
        if dimension >= len(self.intervals):
            return []
        current_rect_list = self._setminus(other, dimension)
        if len(current_rect_list) > 2:
            hrect_list.append(current_rect_list[0])
            hrect_list.append(current_rect_list[1])
            hrect_list.extend(current_rect_list[2].setminus(other, dimension+1))
        else:
            hrect_list.append(current_rect_list[0])
            hrect_list.extend(current_rect_list[1].setminus(other, dimension+1))
        return hrect_list

    def __str__(self):
        return " x ".join([str(i) for i in self.intervals])

    def __repr__(self):
        return "HyperRectangle({})".format(", ".join(map(repr,self.intervals)))

    def __eq__(self, other):
        for i, j in zip(self.intervals, other.intervals):
            if not i == j: return False
        return True

    def __hash__(self):
        return hash(self.intervals)

    def __len__(self):
        return len(self.intervals)

    def __iter__(self):
        return iter(self.intervals)

    def __getitem__(self, key):
        return self.intervals[key]
