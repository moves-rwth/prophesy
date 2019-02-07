import collections.abc
from enum import Enum

import prophesy.adapter.pycarl as pc
import prophesy.data.interval
from prophesy.data.samples import ParameterInstantiation

class Monotonicity(Enum):
    NEGATIVE = 0
    POSITIVE = 1
    NEITHER = 2
    UNKNOWN = 3

class Parameter(pc.Variable):
    """Variable with an associated interval of allowable values. """

    def __init__(self, variable, interval):
        super().__init__(variable)
        self.interval = interval

    def __hash__(self):
        return super().__hash__()

    def __str__(self):
        return "{} {}".format(super().__str__(), self.interval)

    def __eq__(self, other):
        assert hasattr(self, 'interval'), "This object somehow does not have an interval attached"
        return super().__eq__(other) and hasattr(other, 'interval') and self.interval == other.interval

    def __repr__(self):
        return "Parameter({!r}, {!r})".format(super().__str__(), self.interval)

    def __setstate__(self, state):
        super().__setstate__(state[0])
        self.interval = prophesy.data.interval.Interval.__new__(prophesy.data.interval.Interval)
        self.interval.__dict__.update(state[1])


    def __getstate__(self):
        return (super().__getstate__(), self.interval.__dict__)



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

    def update_variables(self, variables):
        new_parameters = ParameterOrder()
        for p in self:
            found = False
            for v in variables:
                if p.name == v.name:
                    new_parameters.append(Parameter(v, p.interval))
                    found = True
            if not found:
                new_parameters.append(p)
        self.clear()
        for p in new_parameters:
            self.append(p)

    def __str__(self):
        return "[{}]".format(", ".join(map(str, self)))

    def instantiate(self, one_or_more_pointlikes):
        """Create ParameterInstantiation(s) from point-like objects.

        Returns the same shape as the input, i.e., if the input is a single
        point-like object (i.e., iterable, hopefully of numbers), returns a
        single ParameterInstantiation; for a list of points, returns a list
        of ParameterInstantiations.
        """
        def looks_like_list_of_points(a):
            return isinstance(a, collections.abc.Sequence) and isinstance(a[0], collections.abc.Sized) and len(a[0]) == len(self)

        def looks_like_a_single_point(a):
            return isinstance(a, collections.abc.Sized) and len(a) == len(self)

        if looks_like_list_of_points(one_or_more_pointlikes):
            return [ParameterInstantiation.from_point(p, self) for p in one_or_more_pointlikes]
        elif looks_like_a_single_point(one_or_more_pointlikes):
            return ParameterInstantiation.from_point(one_or_more_pointlikes, self)
        else:
            raise RuntimeError("Unexpected shape. This *may* be legitimate. See code and possibly add this case.")
