import prophesy.adapter.pycarl as pc
import prophesy.data.interval


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
        return super().__eq__(other) and self.interval == other.interval

    def __repr__(self):
        return "Parameter({!r}, {!r})".format(super().__str__(), self.interval)


class ParameterOrder(list):
    """Class to represent on ordered list of parameters."""

    def get_parameter(self, name):
        """
        Return the parameter with the given name.
        
        :param name: The name of the parameter
        :return: The parameter with the given name
        :rtype: Parameter
        """
        filtered = [p for p in self if p.name == name]
        if len(filtered) == 0:
            raise ValueError("Variable with name {} not found".format(name))
        elif len(filtered) > 2:
            raise RuntimeError("Parameter list got several parameters with the same name")
        return filtered[0]

    def get_variables(self):
        """
        Computes a list of variables corresponding to this ParameterOrder
        
        :return: A list of variables ordered as the parameters
        :rtype: list(pycarl.Variable)
        """
        return [pc.Variable(p.name, p.type) for p in self]  # FIXME ugly

    def get_variable_bounds(self):
        """
        Computes a list of bounds ordered according to this ParameterOrder
        
        :return: list of Interval
        :rtype: list(Interval)
        """
        return [p.interval for p in self]

    def remove_variable(self, variable):
        """
        Remove parameter represented by a given variable
        
        :param variable: A variable whose associated parameter should be removed from the list.
        :return: 
        """
        for p in self:
            if p.id == variable.id:  # FIXME better: custom __eq__ (if even needed? check.)
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
