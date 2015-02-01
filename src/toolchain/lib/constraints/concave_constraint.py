from shapely.geometry import polygon
from shapely.ops import triangulate

def poly_constraint(points, generator):
    assert len(points) >= 3, "Must supply at least 3 points"
    ring = polygon.LinearRing(points)
    complex_poly = polygon.Polygon(ring)
    # CCW polygon
    complex_poly = polygon.orient(complex_poly, 1.0)
    convex_poly = complex_poly.convex_hull
    # If concave (ie convex hull has less points), then split in triangles
    if len(list(complex_poly.exterior.coords)) > len(list(convex_poly.exterior.coords)):
        polys = triangulate(complex_poly)
    else:
        polys = [complex_poly]

    or_constraint = None

    for poly in polys:
        points = list(poly.exterior.coords)
        constraint = generator.compute_constraint(poly)

        if or_constraint is None:
            or_constraint = constraint
        else:
            or_constraint = or_constraint | constraint

    return or_constraint
