from data.constraint import Constraint
from sympy.polys.polytools import Poly

def sortPoints(points):
    """Sortes given list of 2D coordinates clockwise"""
    from math import atan2
    center = (0.0, 0.0)
    for p in points:
        center = (center[0] + p[0], center[1] + p[1])
    center = (center[0] / len(points), center[1] / len(points))
    sorted_points = sorted(points, key = lambda c: atan2(c[0] - center[0], c[1] - center[1]))
    return sorted_points

def poly_constraint(points, parameters):
    assert len(points) >= 3, "Must supply at least 3 points"
    points = sortPoints(points)
    points.append(points[0])
    constraints = []

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

        # TODO: '>=' as plane is marked by RHS (CW), not sure if this applies to n-dimen
        new_constraint = Constraint(Poly(poly - c, parameters), ">=", parameters)
        constraints.append(new_constraint)

    return constraints
