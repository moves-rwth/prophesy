from enum import Enum


class BoundType(Enum):
    open = 0
    closed = 1

    def __int__(self):
        return 0 if self == BoundType.open else 1


def string_to_interval(input_string, internal_parse_func):
    """
    Given a string which encodes an interval, constructs the interval
    
    :param input_string: 
    :param internal_parse_func: 
    :return: The represented interval
    :rtype: Interval
    """
    assert isinstance(input_string, str)
    input_string = input_string.strip()
    if input_string[0] == "(":
        left_bt = BoundType.open
    elif input_string[0] == "[":
        left_bt = BoundType.closed
    else:
        raise RuntimeError("Cannot parse the interval given by: " + input_string + ". Expected '(' or '[' at the start.")

    if input_string[-1] == ")":
        right_bt = BoundType.open
    elif input_string[-1] == "]":
        right_bt = BoundType.closed
    else:
        raise RuntimeError("Cannot parse the interval given by: " + input_string + ". Expected ')' or ']' at the end.")

    inbetween = input_string[1:-1]
    bounds = inbetween.split(",")
    if len(bounds) != 2:
        raise RuntimeError("Cannot parse the interval given by: " + input_string + ". Expected exactly one comma in the interval.")

    left_value = internal_parse_func(bounds[0])
    right_value = internal_parse_func(bounds[1])
    return Interval(left_value, left_bt, right_value, right_bt)


def create_embedded_closed_interval(interval, epsilon):
    """
    For an (half) open interval from l to r, create a closed interval [l+eps, r-eps]. 
    
    :param interval: The interval which goes into the method
    :param epsilon: An epsilon offset used to close.
    :return: A closed interval.
    """

    if interval.is_closed():
        return interval

    if interval.left_bound_type() == BoundType.open:
        if interval.right_bound_type() == BoundType.open:
            if interval.width() <= 2*epsilon:
                raise ValueError("Interval is not large enough.")
            return Interval(interval.left_bound() + epsilon, BoundType.closed, interval.right_bound() - epsilon, BoundType.closed)

    if interval.width() <=  epsilon:
        raise ValueError("Interval is not large enough.")

    if interval.left_bound_type == BoundType.open:
        return Interval(interval.left_bound + epsilon, BoundType.closed, interval.right_bound(),
                        BoundType.closed)
    return Interval(interval.left_bound, BoundType.closed, interval.right_bound() - epsilon,
                    BoundType.closed)


class Interval:
    """
    Interval class for arbitrary (constant) types.
    Construction from string is possible via string_to_interval
    TODO support half-bounded intervals (e.g some value for infty)
    """
    def __init__(self, left_value, left_bt, right_value, right_bt):
        self._left_bound_type = left_bt
        self._left_value = left_value
        self._right_bound_type = right_bt
        self._right_value = right_value

    def left_bound(self):
        return self._left_value

    def right_bound(self):
        return self._right_value

    def left_bound_type(self):
        return self._left_bound_type

    def right_bound_type(self):
        return self._right_bound_type

    def empty(self):
        """
        Does the interval contain any points.
        
        :return: True, iff there exists a point in the interval.
        """
        if self._left_value == self._right_value:
            return (self._left_bound_type == BoundType.open or self._right_bound_type == BoundType.open)
        return self._left_value > self._right_value

    def contains(self, pt):
        """
        Does the interval contain a specific point
        
        :param pt: A value
        :return: True if the value lies between the bounds.
        """
        if self._left_value < pt < self._right_value: return True
        if pt == self._left_value and self._left_bound_type == BoundType.closed: return True
        if pt == self._right_value and self._right_bound_type == BoundType.closed: return True
        return False

    def is_closed(self):
        """
        Does the interval have closed bounds on both sides.
        
        :return: True iff both bounds are closed.
        """
        return self.right_bound_type() == BoundType.closed and self.left_bound_type() == BoundType.closed

    def width(self):
        """
        The width of the interval
        
        :return: right bound - left bound
        """
        return self._right_value - self._left_value

    def split(self):
        """
        Split the interval in two equally large halfs.
        
        :return: Two intervals, the first from the former left bound to (excluding) middle point (leftbound + rightbound)/2, 
                                the second from the middle point (including) till the former right bound
        """
        mid = self._left_value + self.width() / 2
        return Interval(self._left_value, self._left_bound_type, mid, BoundType.open), Interval(mid, BoundType.closed, self._right_value, self._right_bound_type)

    def close(self):
        """
        Make all bounds closed
        
        :return: A new interval which has closed bounds instead.
        """
        return Interval(self._left_value, BoundType.closed, self._right_value, BoundType.closed)

    def intersect(self, other):
        """
        Compute intersection between to intervals
        
        :param other: 
        :return: 
        """
        assert isinstance(other, Interval)
        if self._left_value > other._left_value:
            newleft = self._left_value
            newLB = self._left_bound_type
        elif self._left_value < other._left_value:
            newleft = other._left_value
            newLB = other._left_bound_type
        else:
            newleft = self._left_value
            newLB = self._left_bound_type if self._left_bound_type == BoundType.open else other._left_bound_type
        if self._right_value < other._right_value:
            newright = self._right_value
            newRB = self._right_bound_type
        elif self._right_value > other._right_value:
            newright = other._right_value
            newRB = other._right_bound_type
        else:
            newright = self._right_value
            newLB = self._right_bound_type if self._right_bound_type == BoundType.open else other._right_bound_type
        return Interval(newleft, newLB, newright, newRB)

    def __str__(self):
        return ("(" if self._left_bound_type == BoundType.open else "[") + str(self._left_value) + "," + str(self._right_value) + (")" if self._right_bound_type == BoundType.open else "]")

    def __repr__(self):
        return ("(" if self._left_bound_type == BoundType.open else "[") + repr(self._left_value) + "," + repr(self._right_value) + (")" if self._right_bound_type == BoundType.open else "]")

    def __eq__(self, other):
        assert isinstance(other, Interval)
        if self.empty() and other.empty(): return True
        if not self._left_bound_type == other._left_bound_type: return False
        if not self._left_value == other._left_value: return False
        if not self._right_bound_type == other._right_bound_type: return False
        if not self._right_value == other._right_value: return False
        return True

    def __hash__(self):
        return hash(self._left_value) ^ hash(self._right_value) + int(self._left_bound_type) + int(self._right_bound_type)
