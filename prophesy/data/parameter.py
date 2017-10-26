import collections

import prophesy.adapter.pycarl as pc
import prophesy.data.interval
from prophesy.data.samples import ParameterInstantiation


class Parameter(pc.Variable):
    """Variable with an associated interval of allowable values. """

    def __init__(self, variable, interval):
        super().__init__(variable.name, variable.type)
        self.interval = interval

    def __hash__(self):
        return super().__hash__() ^ hash(self.interval)

    def __str__(self):
        return "{} {}".format(super().__str__(), self.interval)

    def __eq__(self, other):
        return (
            super().__eq__(other) and
            hasattr(other, 'interval') and
            self.interval == other.interval
        )

    def __repr__(self):
        return "Parameter({!r}, {!r})".format(super().__str__(), self.interval)


class ParameterOrder(list):
    """Class to represent on ordered list of parameters."""

    def get_parameter(self, name):
        """Return the parameter with the given name."""
        filtered = [p for p in self if p.name == name]
        if len(filtered) == 0:
            raise ValueError("Variable with name {} not found".format(name))
        elif len(filtered) > 1:
            raise RuntimeError("Parameter list got several parameters with the same name")
        return filtered[0]

    def get_parameter_bounds(self):
        """Computes a list of bounds ordered according to this ParameterOrder.

        :return: list of Interval
        :rtype: list(Interval)
        """
        return [p.interval for p in self]

    def remove_parameter(self, parameter):
        """Remove parameter represented by a given variable."""
        for p in self:
            if p == parameter or type(parameter) == pc.Variable and super(Parameter, p).__eq__(parameter):
                self.remove(p)
                return

    def make_intervals_closed(self, epsilon):
        """
        For several applications, we want to have an embedded closed interval 
        
        :param epsilon: How far from an open bound should the embedded interval-bound be away
        """
        for p in self:
            p.interval = prophesy.data.interval.create_embedded_closed_interval(p.interval, epsilon)

    def make_intervals_open(self):
        for p in self:
            p.interval = p.interval.open()

    def __str__(self):
        return "[{}]".format(", ".join(map(str, self)))

    def instantiate(self, one_or_more_pointlikes):
        def looks_like_list_of_points(a):
            return isinstance(a, collections.Sequence) and isinstance(a[0], collections.Sized) and len(a[0]) == len(self)

        def looks_like_a_single_point(a):
            return isinstance(a, collections.Sized) and len(a) == len(self)

        if looks_like_list_of_points(one_or_more_pointlikes):
            return [ParameterInstantiation.from_point(p, self) for p in one_or_more_pointlikes]
        elif looks_like_a_single_point(one_or_more_pointlikes):
            return ParameterInstantiation.from_point(one_or_more_pointlikes, self)
        else:
            raise RuntimeError("Unexpected shape. This *may* be legitimate. See code and possibly add this case.")
