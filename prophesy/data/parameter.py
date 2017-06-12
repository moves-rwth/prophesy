import prophesy.data.interval

class Parameter(object):
    """Class representing a parameter, which is a variable with an associated
    interval of allowable values.
    """

    def __init__(self, variable, interval):
        """
        @param variable pycarl.Variable
        @param interval Interval
        """
        self.variable = variable
        self.interval = interval

    def __str__(self):
        return "{} {}".format(self.variable, self.interval)

    def __repr__(self):
        return "Parameter({!r}, {!r})".format(self.variable, self.interval)

class ParameterOrder(list):
    """Class to represent on ordered list of parameters
    """

    def get_variable(self, name):
        filter = [p.variable for p in self if p.variable.name == name]
        if filter == []:
            raise ValueError("Variable with name {} not found".format(name))
        elif len(filter) > 2:
            raise RuntimeError("Parameter list got several parameters with the same name")
        return filter[0]

    def get_variables(self):
        """Returns a VariableOrder corresponding to this ParameterOrder
        @return VariableOrder
        """
        return list([p.variable for p in self])

    def get_variable_bounds(self):
        """Returns a list of bounds ordered according to this ParameterOrder
        @return list of Interval
        """
        return [p.interval for p in self]

    def make_intervals_closed(self, epsilon):
        """
        For several applications, we want to have an embedded closed interval 
        :param epsilon: How far from an open bound should the embedded interal-bound be away
        """
        for p in self:
            p.interval = prophesy.data.interval.create_embedded_closed_interval(p.interval, epsilon)

    def __str__(self):
        return "[{}]".format(", ".join(map(str, self)))


