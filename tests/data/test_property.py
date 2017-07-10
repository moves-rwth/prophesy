from prophesy.data.property import *
import prophesy.adapter.pycarl as pc


def test_property_parsing():
    input_string = "Pmin=? [F \"now\"]"
    p = Property.from_string(input_string)
    assert input_string == str(p)
    input_string = "Pmin=? [F \"now\"]"
    p = Property.from_string(input_string)
    assert input_string == str(p)
    input_string = "P>=3/4 [F \"now\"]"
    p = Property.from_string(input_string)
    assert input_string == str(p)
    input_string = "P<=0.4 [F \"now\"]"
    p = Property.from_string(input_string)
    assert p.operator_direction == OperatorDirection.unspecified
    assert p.bound.threshold == pc.Rational(pc.Integer(2), pc.Integer(5))
