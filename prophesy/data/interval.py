from enum import Enum

class BoundType(Enum):
    open = 0
    closed = 1


def string_to_interval(input, internal_parse_func):
    assert isinstance(input, str)
    input = input.strip()
    left_bt = None
    if input[0] == "(":
        left_bt = BoundType.open
    elif input[0] == "[":
        left_bt = BoundType.closed
    else:
        raise RuntimeError("Cannot parse the interval given by: " + input + ". Expected '(' or '[' at the start.")

    right_bt = None
    if input[-1] == ")":
        right_bt = BoundType.open
    elif input[-1] == "]":
        right_bt = BoundType.closed
    else:
        raise RuntimeError("Cannot parse the interval given by: " + input + ". Expected ')' or ']' at the end.")

    inbetween = input[1:-1]
    bounds = inbetween.split(",")
    if len(bounds) != 2:
        raise RuntimeError("Cannot parse the interval given by: " + input + ". Expected exactly one comma in the interval.")

    left_value = internal_parse_func(bounds[0])
    right_value = internal_parse_func(bounds[1])
    return Interval(left_value, left_bt, right_value, right_bt)


class Interval:
    """
    Interval class for arbitrary types
    """
    def __init__(self, left_value, left_bt, right_value, right_bt ):
        self._left_bound_type = left_bt
        self._left_value = left_value
        self._right_bound_type = right_bt
        self._right_value = right_value

    def __str__(self):
        return ("(" if self._left_bound_type == BoundType.open else "[") + str(self._left_value) + "," + str(self._right_value) + (")" if self._right_bound_type == BoundType.open else "]")

    def left_bound(self):
        return self._left_value

    def right_bound(self):
        return self._right_value

    def left_bound_type(self):
        return self._left_bound_type

    def right_bound_type(self):
        return self._right_bound_type