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

    def __eq__(self, other):
        assert isinstance(other, Interval)
        if self.empty() and other.empty(): return True
        if not self._left_bound_type == other._left_bound_type: return False
        if not self._left_value == other._left_value: return False
        if not self._right_bound_type == other._right_bound_type: return False
        if not self._right_value == other._right_value: return False
        return True

    def left_bound(self):
        return self._left_value

    def right_bound(self):
        return self._right_value

    def left_bound_type(self):
        return self._left_bound_type

    def right_bound_type(self):
        return self._right_bound_type

    def empty(self):
        if self._left_value > self._right_value: return False
        if self._left_value == self._right_value and (self._left_bound_type == BoundType.open or self._right_bound_type == BoundType.open): return False

    def contains(self, pt):
        if self._left_value < pt < self._right_value: return True
        if pt == self._left_value and self._left_bound_type == BoundType.closed: return True
        if pt == self._right_value and self._right_bound_type == BoundType.closed: return True
        return False

    def width(self):
        return self._right_value - self._left_value

    def split(self):
        mid = self._left_value + self.width()/2
        return Interval(self._left_value, self._left_bound_type, mid, BoundType.open), Interval(mid, BoundType.closed, self._right_value, self._right_bound_type)

    def close(self):
        return Interval(self._left_value, BoundType.closed, self._right_value, BoundType.closed)

    def intersect(self, other):
        assert isinstance(other, Interval)
        if self._left_value > other._left_value:
            newleft = self._left_value
            newLB = self._left_bound_type
        elif self._left_value < other._left_value:
            newleft = other._left_value
            newLB = other._left_bound_type
        else:
            newleft = self._left_value
            newLB = self._left_bound_type if self.left_bound_type == BoundType.open else other._left_bound_type
        if self._right_value < other._right_value:
            newright = self._right_value
            newRB = self._right_bound_type
        elif self._right_value > other._right_value:
            newright = other._right_value
            newRB = other._right_bound_type
        else:
            newright = self._right_value
            newLB = self._right_bound_type if self.right_bound_type == BoundType.open else other._right_bound_type
        return Interval(newleft, newLB, newright, newRB)