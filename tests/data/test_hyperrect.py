from prophesy.data.interval import Interval, string_to_interval, BoundType
from prophesy.data.hyperrectangle import HyperRectangle
import prophesy.adapter.pycarl as pc


def test_get_middle_component():
    h1 = HyperRectangle(string_to_interval("[-10,10]",float))
    h2 = HyperRectangle(string_to_interval("[-5,5]", float))
    hlist = h1._setminus(h2, 0)
    assert hlist[0] == HyperRectangle(string_to_interval("[-10,-5)",float)) and \
            hlist[1] == HyperRectangle(string_to_interval("(5,10]", float)) and \
            hlist[2] == HyperRectangle(string_to_interval("(-5, 5)", float))


def test_setminus_hyperrectangles():
    h1 = HyperRectangle(string_to_interval("[0,1]",float),string_to_interval("[0,1]",float))
    h2 = HyperRectangle(string_to_interval("[0.2,0.75]",float),string_to_interval("[0.3,0.6]",float))
    hlist = h1.setminus(h2)
    assert hlist[0] == HyperRectangle(string_to_interval("[0.0,0.2)",float), string_to_interval("[0.0,1.0]", float)) and \
            hlist[1] == HyperRectangle(string_to_interval("(0.75, 1.0]",float), string_to_interval("[0.0,1.0]",float)) and \
            hlist[2] == HyperRectangle(string_to_interval("(0.2,0.75)",float), string_to_interval("[0.0,0.3)",float)) and \
            hlist[3] == HyperRectangle(string_to_interval("(0.2,0.75)",float), string_to_interval("(0.6, 1.0]", float))

def test_region_string():
    h2 = HyperRectangle(string_to_interval("[2,5]",pc.Rational),string_to_interval("[3,6]",pc.Rational))
    variables = [pc.Variable("x"), pc.Variable("y")]
    h3 = HyperRectangle.from_region_string(h2.to_region_string(variables), variables)
    assert h2 == h3