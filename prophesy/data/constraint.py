from prophesy.adapter.pycarl import Polynomial, Rational
import prophesy.adapter.pycarl as pc
from shapely.geometry.polygon import LinearRing, Polygon, orient


def region_from_polygon(polygon, variables):
    """Compute formula representing  polygon (Polygon, LineString or LinearRing).

    Area will be considered at the rhs (ccw) of line segments.

    :param polygon: Polygon, LineString or LinearRing, must be convex
    :return: Formula s.t. points in polygon are satisfied.
    :rtype: pycarl.Formula or pycarl.Constraint
    """
    if len(variables) > 2:
        raise ValueError("The method is only available for two dimensional polygons.")

    if isinstance(polygon, LinearRing):
        # Convert to polygon so it can be oriented
        polygon = Polygon(polygon)

    if isinstance(polygon, Polygon):
        assert len(list(polygon.interiors)) == 0
        polygon = orient(polygon, sign=1.0)
        polygon = polygon.exterior
    points = [(Rational(c1), Rational(c2)) for c1, c2 in list(polygon.coords)]
    assert len(points) >= 2

    constraint = None
    # Calculate half-plane for each pair of points
    # http://math.stackexchange.com/questions/82151/find-the-equation-of-the-plane-passing-through-a-point-and-a-vector-orthogonal
    for p1, p2 in zip(points[:-1], points[1:]):
        # Get vector direction (parallel to hyperplane)
        dvec = tuple([c2 - c1 for c1, c2 in zip(p1, p2)])
        # Make vector orthogonal to hyperplane
        # NOTE: rotate clockwise
        dvec = (dvec[1], -dvec[0])

        # Constant is dot-product of directional vector and origin
        c = sum([c1 * c2 for c1, c2 in zip(dvec, p1)])
        # Construct polynomial for line
        poly = Polynomial(-Rational(c))
        for variable, coefficient in zip(variables, dvec):
            if coefficient != 0:
                # FIXME Parameter / Variable !5
                poly = poly + Polynomial(variable) * coefficient

    new_constraint = pc.Constraint(poly, pc.Relation.LEQ)
    if constraint is None:
        constraint = new_constraint
    else:
        constraint = constraint & new_constraint

    return constraint
