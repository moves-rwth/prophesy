'''
Created on 19 Apr 2016

@author: hbruintjes
'''
from prophesy.data.variable import VariableOrder
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

class ParameterOrder(list):
    """Class to represent on ordered list of parameters
    """

    def get_variable_order(self):
        """Returns a VariableOrder corresponding to this ParameterOrder
        @return VariableOrder
        """
        return VariableOrder([p.variable for p in self])

    def get_variable_bounds(self):
        """Returns a list of bounds ordered according to this ParameterOrder
        @return list of Interval
        """
        return [p.interval for p in self]
