from prophesy.data.interval import Interval
from prophesy.data.point import Point
import prophesy.adapter.pycarl as pc
from prophesy.data.interval import BoundType

# TOOD remove numpy?
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
    def from_extremal_points(cls, lowerpoint, upperpoint, boundtype):
        """
        :param lowerpoint: A point corresponding to the lower boundary
        :param upperpoint: A point corresponding to the upper boundary
        :param boundtype: BoundType to use as bounds for the resulting
            HyperRectangle
        :return HyperRectangle
        """
        return cls.__init__(*[Interval(l, boundtype, r, boundtype) for l, r in zip(lowerpoint, upperpoint)])

    def dimension(self):
        return len(self.intervals)

    def empty(self):
        for interv in self.intervals:
            if interv.empty():
                return True
        return False

    def vertices(self):
        result = []
        for i in range(0, pow(2, self.dimension()), 1):
            num_bits = self.dimension()
            bits = [(i >> bit) & 1 for bit in range(num_bits - 1, -1, -1)]
            result.append(Point(
                *[(self.intervals[i].left_bound() if x == 0 else self.intervals[i].right_bound()) for i, x in
                  zip(range(0, self.dimension()), bits)]))
        return result

    def center(self):
        return Point(*[interval.center() for interval in self.intervals])

    def np_vertices(self):
        verts = self.vertices()
        return np.array([np.array(list(map(float, v))) for v in verts])

    # def vertices_and_inward_dir(self):

    def split_in_every_dimension(self):
        """
        Splits the hyperrectangle in every dimension
        :return: The 2^n many hyperrectangles obtained by the split
        """
        result = []
        splitted_intervals = [tuple(interv.split()) for interv in self.intervals]
        for i in range(0, pow(2, self.dimension()), 1):
            num_bits = self.dimension()
            bits = [(i >> bit) & 1 for bit in range(num_bits - 1, -1, -1)]
            result.append(HyperRectangle(*[splitted_intervals[i][x] for i, x in zip(range(0, self.dimension()), bits)]))
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

    def is_closed(self):
        """
        Checks whether the hyperrectangle is closed in every dimension.
        :return: True iff all intervals are closed.
        """
        for i in self.intervals:
            if not i.is_closed():
                return False
        return True

    def close(self):
        return HyperRectangle(*[i.close() for i in self.intervals])

    def _setminus(self, other, dimension):
        """
        Helper function for setminus
        :param other: 
        :param dimension: 
        :return: 
        """
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
        Does a setminus operation on hyperrectangles and returns a list with hyperrects covering the resulting area
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
            hrect_list.extend(current_rect_list[2].setminus(other, dimension + 1))
        else:
            hrect_list.append(current_rect_list[0])
            hrect_list.extend(current_rect_list[1].setminus(other, dimension + 1))
        return hrect_list

    def __str__(self):
        return " x ".join([str(i) for i in self.intervals])

    def __repr__(self):
        return "HyperRectangle({})".format(", ".join(map(repr, self.intervals)))

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

    def to_formula(self, variables):
        """Given HyperRectangle and VariableOrder, compute constraints
        @param hyperrectangle HyperRectangle
        @param variables VariableOrder
        @return pycarl.Formula or pycarl.Constraint
        """
        constraint = None
        for variable, interval in zip(variables, self.intervals):
            lbound_relation = pc.Relation.GEQ if interval.left_bound_type() == BoundType.closed else pc.Relation.GREATER
            lbound = pc.Constraint(pc.Polynomial(variable) - interval.left_bound(), lbound_relation)
            if constraint is None:
                constraint = lbound
            else:
                constraint = constraint & lbound
            rbound_relation = pc.Relation.LEQ if interval.right_bound_type() == BoundType.closed else pc.Relation.LESS
            rbound = pc.Constraint(pc.Polynomial(variable) - interval.right_bound(), rbound_relation)
            constraint = constraint & rbound
        return constraint

    def to_region_string(self, variables):
        """
        Constructs a region string, as e.g. used by storm-pars
        :param variables: An ordered list of the variables
        :type variables: List[pycarl.Variable]
        :return: 
        """
        if not self.is_closed():
            raise ValueError("Region strings are only defined for closed intervals")
        var_strings = []
        for variable, interval in zip(variables, self.intervals):
            var_strings.append("{}<={}<={}".format(interval.left_bound(), str(variable), interval.right_bound()))
        return ",".join(var_strings)

    @classmethod
    def from_region_string(cls, input_string, variables):
        """
        Constructs a hyperrectangle with dimensions according to the variable order.
        :param input: 
        :param variables: 
        :return: A HyperRectangle
        """
        interval_strings = input_string.split(",")
        variables_to_intervals = dict()
        for int_str in interval_strings:
            components = int_str.split("<=")
            if len(components) != 3:
                raise ValueError("Expected string in the form Number<=Variable<=Number, got {}".format(int_str))
            variables_to_intervals[components[1]] = Interval(pc.Rational(components[0]), BoundType.closed,
                                                             pc.Rational(components[2]), BoundType.closed)
        ordered_intervals = []
        for variable in variables:
            ordered_intervals.append(variables_to_intervals[variable.name])
        # TODO checks.
        return cls(*ordered_intervals)
