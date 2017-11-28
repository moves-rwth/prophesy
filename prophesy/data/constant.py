import prophesy.adapter.pycarl as pc
from prophesy.data.parameter import Parameter


class Constants(dict):
    """Container that holds constants for a model."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def to_key_value_string(self, to_float=False):
        """Provides a key-value string from variable to constant value.

        The key-value string format can be immediately used for storm or prism.
        
        :param to_float: Should the constant value be casted into a float
        :return: A string of the format var1=val1,...,varn=valn
        """
        key_value_list = list(self.items())

        if to_float:
            key_value_list = [(var, float(val) if isinstance(val, pc.Rational) else val) for var, val in key_value_list]

        return ",".join(["{}={}".format(var.name, val.name if isinstance(val, pc.Variable) else val) for var, val in key_value_list])

    def __contains__(self, item):
        # FIXME when Parameter is Variable
        if isinstance(item, Parameter):
            return any((v.name == item.name for v in self.keys()))
        else:
            return super().__contains__(item)


def parse_constants_string(input_string):
    """
    Parses a key-value string 
    
    :param input_string: 
    :return: 
    """
    result = Constants()
    if input_string is None or input_string == "":
        return result
    defs = input_string.split(",")
    for constant_def in defs:
        constant_and_def = constant_def.split("=")
        if len(constant_and_def) != 2:
            raise ValueError("Expected key-value pair, found {}".format(constant_def))
        var = pc.variable_with_name(constant_and_def[0])
        if var.is_no_variable:
            var = pc.Variable(constant_and_def[0])
        val = pc.parse(constant_and_def[1])
        result[var] = val
    return result
