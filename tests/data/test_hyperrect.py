from prophesy.data.interval import Interval, string_to_interval, BoundType
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.data.point import Point
import prophesy.adapter.pycarl as pc



def test_hyperrectangle_splitting():
    i = Interval(0.0, BoundType.closed, 2.0, BoundType.closed)
    j = Interval(4.0, BoundType.open, 8.0, BoundType.closed)
    r = HyperRectangle(i,j)
    res = r.split_in_every_dimension()
    i00 = HyperRectangle(Interval(0.0, BoundType.closed, 1.0, BoundType.open), Interval(4.0, BoundType.open, 6.0, BoundType.open))
    i01 = HyperRectangle(Interval(0.0, BoundType.closed, 1.0, BoundType.open), Interval(6.0, BoundType.closed, 8.0, BoundType.closed))
    assert i00 in res
    assert i01 in res
    i00 = HyperRectangle(Interval(1.0, BoundType.closed, 2.0, BoundType.closed), Interval(4.0, BoundType.open, 6.0, BoundType.open))
    i01 = HyperRectangle(Interval(1.0, BoundType.closed, 2.0, BoundType.closed), Interval(6.0, BoundType.closed, 8.0, BoundType.closed))
    assert i00 in res
    assert i01 in res


def test_hyperrectangle_vertices():
    i = Interval(0.0, BoundType.closed, 2.0, BoundType.closed)
    j = Interval(4.0, BoundType.closed, 8.0, BoundType.closed)
    r = HyperRectangle(i,j)
    vertices  = r.vertices()
    assert len(vertices) == 4
    assert Point(0.0, 4.0) in vertices
    assert Point(2.0, 4.0) in vertices


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