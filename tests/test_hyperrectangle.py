from prophesy.data.interval import Interval, BoundType
from prophesy.data.hyperrectangle import HyperRectangle

def test_hyperrectangle_splitting():
    i = Interval(0.0, BoundType.closed, 2.0, BoundType.closed)
    j = Interval(4.0, BoundType.open, 8.0, BoundType.closed)
    r = HyperRectangle(i,j)
    res = r.split_in_every_dimension()
    i00 = HyperRectangle([Interval(0.0, BoundType.closed, 1.0, BoundType.open), Interval(4.0, BoundType.open, 6.0, BoundType.open)])
    i01 = HyperRectangle([Interval(0.0, BoundType.closed, 1.0, BoundType.open), Interval(6.0, BoundType.closed, 8.0, BoundType.closed)])
    i00 = HyperRectangle([Interval(1.0, BoundType.closed, 2.0, BoundType.closed), Interval(4.0, BoundType.open, 6.0, BoundType.open)])
    i01 = HyperRectangle([Interval(1.0, BoundType.closed, 2.0, BoundType.closed), Interval(6.0, BoundType.closed, 8.0, BoundType.closed)])
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