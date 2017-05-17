from prophesy.data.point import Point

def test_to_float():
    p = Point(*[3, 4]).to_float()
    assert p[0] == 3.0


