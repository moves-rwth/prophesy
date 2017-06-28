
from prophesy.adapter.pycarl import Polynomial, Rational, parse
import prophesy.adapter.pycarl as pc
from shapely.geometry.polygon import LinearRing, Polygon, orient
from prophesy.data.samples import ParameterInstantiation


def parse_constraint(constraint_str):
    args = constraint_str.split(",")
    if len(args) != 2:
        raise ValueError("Constraint string should be of the form <rational function>,<relation>, but is {}".format(constraint_str))
    res = parse(args[0])
    rel = parse_relation(args[1])
    return res


def parse_relation(relation_string):
    if relation_string == ">=":
        return pc.Relation.GEQ
    elif relation_string == "<=":
        return pc.Relation.LEQ
    elif relation_string == "<":
        return pc.Relation.LESS
    elif relation_string == ">":
        return pc.Relation.GREATER
    raise ValueError("Cannot parse {} as a relation".format(relation_string))


def region_from_polygon(polygon, variables):
        """Compute regions from polygon (Polygon, LineString or LinearRing)
        Area will be considered at the rhs (ccw) of line segments
        @param polygon Polygon, LineString or LinearRing, must be convex
        @return pycarl.Formula or pycarl.Constraint
        """
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
            # TODO: 2D only
            dvec = (dvec[1], -dvec[0])

            # Constant is dot-product of directional vector and origin
            c = sum([c1 * c2 for c1, c2 in zip(dvec, p1)])
            # Construct polynomial for line
            poly = Polynomial(-Rational(c))
            for variable, coefficient in zip(variables, dvec):
                if coefficient != 0:
                    poly = poly + Polynomial(variable) * coefficient

            # TODO: '<=' as polygon is CCW oriented, not sure if this applies to n-dimen
            new_constraint = pc.Constraint(poly, pc.Relation.LEQ)
            if constraint is None:
                constraint = new_constraint
            else:
                constraint = constraint & new_constraint

        return constraint


def is_point_fulfilling_constraint(pt, constraint):
    """Check whether the given point is satisfied by the regions
    (i.e. is contained by it)
    @param pt SamplePoint
    @param constraint pycarl.formula.Constraint or pycarl.formula.Formula
    """
    assert isinstance(pt, ParameterInstantiation)
    return constraint.satisfied_by(pt)
