import prophesy.adapter.pycarl as pc


class Constant(object):
    """
    A variable and its constant value.
    """

    def __init__(self, variable, value):
        """
        Initialise the constant
        
        :param variable:  pycarl.Variable which encodes the constant
        :param value: expression for the value of the constant
        """
        self.variable = variable
        self.value = value

    @property
    def name(self):
        """
        
        :return: The name of the variable representing the constant 
        """
        return self.variable.name

class Constants(object):
    """
    Container that holds constants for a model. 
    """
    def __init__(self):
        self.constants = dict()

    def has_variable(self, var):
        """
        Does the container contain a constant encoded by the given variable?
        
        :param var: The variable which might be contained.
        :return: 
        """
        return var in self.constants

    def get_constant(self, var):
        """
        Get the constant associated with the given variable 
        
        :param var: 
        :return: 
        """
        return self.constants[var]

    def add(self, constant):
        """
        Add a constant.
        
        :param constant: 
        :return: 
        """
        self.constants[constant.variable] = constant

    def to_key_value_string(self, to_float=False):
        """
        Provides a key-value string from variable to constant value.
        The key-value string format can be immediately used for storm or prism.
        
        :param to_float: Should the constant value be casted into a float
        :return: A string of the format var1=val1,...,varn=valn
        """
        key_value_list = [(k,v.value) for k, v in self.constants.items()]
        if to_float:
            for i in range(len(key_value_list)):
                if isinstance(key_value_list[i][1], pc.Rational):
                    key_value_list[i] = (key_value_list[i][0], float(key_value_list[i][1]))

        return ",".join(["{}={}".format(k,v) for k,v in key_value_list])

    def variables(self):
        """
        The set of variables which represent the constants contained.
        
        :return: A iterable over the variables.
        """
        return self.constants.keys()

    def __str__(self):
        return str(self.constants)

    def __len__(self):
        return len(self.constants)


def parse_constants_string(input_string):
    """
    Parses a key-value string 
    
    :param input_string: 
    :return: 
    """
    result = Constants()
    if input_string is None:
        return result
    defs = input_string.split(",")
    for constant_def in defs:
        constant_and_def = constant_def.split("=")
        if len(constant_and_def) != 2:
            raise ValueError("Expected key-value pair, found {}".format(constant_def))
        c = Constant(pc.Variable(constant_and_def[0]), pc.parse(constant_and_def[1]))
        result.add(c)
    return result
