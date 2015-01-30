from data.constraint import Constraint
from sympy.polys.polytools import Poly
from shapely.geometry import polygon
from shapely.ops import triangulate

def poly_constraint(points, parameters):
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
        constraint = None

        # Calculate half-plane for each pair of points
        # http://math.stackexchange.com/questions/82151/find-the-equation-of-the-plane-passing-through-a-point-and-a-vector-orthogonal
        for p1, p2 in zip(points[:-1], points[1:]):
            # Get vector direction (parallel to hyperplane)
            dvec = tuple([c2 - c1 for c1, c2 in zip(p1, p2)])
            # Make vector orthogonal to hyperplane
            # NOTE: rotate clockwise
            # TODO: 2D only
            dvec = (dvec[1], -dvec[0])

            # Constant is dot-product of directional vector and origin
            c = sum([c1 * c2 for c1, c2 in zip(dvec, p1)])
            poly = parameters[0] * dvec[0]
            for i in range(1, len(dvec)):
                poly = poly + parameters[i] * dvec[i]

            # TODO: '<=' as polygon is CCW oriented, not sure if this applies to n-dimen
            new_constraint = Constraint(Poly(poly - c, parameters), "<=", parameters)
            if constraint is None:
                constraint = new_constraint
            else:
                constraint = constraint & new_constraint

        if or_constraint is None:
            or_constraint = constraint
        else:
            or_constraint = or_constraint | constraint

    return or_constraint
