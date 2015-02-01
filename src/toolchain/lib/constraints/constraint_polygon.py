from constraint_generation import ConstraintGeneration
from shapely.ops import triangulate

class ConstraintPolygon(ConstraintGeneration):

    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc):
        ConstraintGeneration.__init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc)

        self.safe_polygons = []
        self.bad_polygons = []

    def change_current_constraint(self):
        # TODO inform user
        return None

    def accept_constraint(self, constraint, safe, safe):
        pass

    def reject_constraint(self, constraint, sample):
        pass

    def next_constraint(self):
        if len(self.safe_polygons) > 0:
            poly = self.safe_polygons[0]
            self.safe_polygons = self.safe_polygons[1:]
            return (self.poly_constraint(poly), poly, True)
        elif len(self.bad_polygons) > 0:
            poly = self.bad_polygons[0]
            self.bad_polygons = self.bad_polygons[1:]
            return (self.poly_constraint(poly), poly, False)

        return None

    def add_polygon(self, polygon, safe):
        if safe:
            self.safe_polygons.append(polygon)
        else:
            self.bad_polygons.append(polygon)

    def poly_constraint(self, complex_poly):
        assert len(complex_poly.exterior.coords) >= 3, "Must supply at least 3 points"
        # CCW polygon
        complex_poly = complex_poly.orient(complex_poly, 1.0)
        convex_poly = complex_poly.convex_hull
        # If concave (ie convex hull has less points), then split in triangles
        if len(list(complex_poly.exterior.coords)) > len(list(convex_poly.exterior.coords)):
            polys = triangulate(complex_poly)
        else:
            polys = [complex_poly]

        or_constraint = None

        for poly in polys:
            constraint = self.compute_constraint(poly)

            if or_constraint is None:
                or_constraint = constraint
            else:
                or_constraint = or_constraint | constraint

        return or_constraint
