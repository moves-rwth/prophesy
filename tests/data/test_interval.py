from prophesy.data.interval import Interval, string_to_interval, BoundType

def test_interval_parsing():
    int1 = string_to_interval("(2,5)", int)
    assert int1.left_bound() == 2
    assert int1.left_bound_type() == BoundType.open
    assert int1.right_bound() == 5
    assert int1.right_bound_type() == BoundType.open
    assert str(int1) == "(2,5)";
    int1 = string_to_interval("(2,7]", int)
    assert int1.left_bound() == 2
    assert int1.left_bound_type() == BoundType.open
    assert int1.right_bound() == 7
    assert int1.right_bound_type() == BoundType.closed
    assert str(int1) == "(2,7]";