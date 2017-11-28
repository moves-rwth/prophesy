from prophesy.data.constant import parse_constants_string
import prophesy.adapter.pycarl as pc


def test_constants_parsing():
    x_var = pc.Variable("x")
    y_var = pc.Variable("y")
    constants = parse_constants_string("x=y,y=2")
    assert x_var in constants
    assert y_var in constants
    constants = parse_constants_string("z=y,a=2")
    z_var = pc.variable_with_name("z")
    assert z_var in constants
    assert "a=2" in constants.to_key_value_string()
    assert "z=y" in constants.to_key_value_string()
