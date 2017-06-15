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


class Constants(object):
    def __init__(self):
        self.constants = dict()

    def has_variable(self, var):
        return var in self.constants

    def get_constant(self, var):
        return self.constants[var]

    def add(self, constant):
        self.constants[constant.variable] = constant

    def to_key_value_string(self, to_float=False):
        key_value_list = [(k,v.value) for k, v in self.constants.items()]
        if to_float:
            for i in range(len(key_value_list)):
                if type(key_value_list[i][1]) is pc.Rational:
                    key_value_list[i] = (key_value_list[i][0], float(key_value_list[i][1]))

        return ",".join(["{}={}".format(k,v) for k,v in key_value_list])

    def variables(self):
        return self.constants.keys()

    def __str__(self):
        return str(self.constants)

    def __len__(self):
        return len(self.constants)


def parse_constants_string(input_string):
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
