from prophesy.data.range import Range, create_cartesian_product


def test_cartesian_product():
    r1 = Range(1, 3, 1)
    r2 = Range(4, 6, 1)
    result = create_cartesian_product([r1, r2])
    assert len(list(result)) == 9
