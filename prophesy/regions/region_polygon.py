from prophesy.regions.region_generation import RegionGenerator
from shapely.ops import triangulate
from shapely.geometry.polygon import orient

class ConstraintPolygon(RegionGenerator):
    def __init__(self, samples, parameters, threshold, threshold_area, _smt2interface, _ratfunc):
        RegionGenerator.__init__(self, samples, parameters, threshold, threshold_area, _smt2interface, _ratfunc)

        self.safe_polygons = []
        self.bad_polygons = []

    def fail_constraint(self, constraint, safe):
        # TODO inform user
        # TODO: convex constraint might be split in triangles
        return None

    def accept_constraint(self, constraint, safe):
        pass

    def reject_constraint(self, constraint, safe, sample):
        pass

    def next_constraint(self):
        if len(self.safe_polygons) > 0:
            poly = self.safe_polygons[0]
            self.safe_polygons = self.safe_polygons[1:]
            return poly, True
        elif len(self.bad_polygons) > 0:
            poly = self.bad_polygons[0]
            self.bad_polygons = self.bad_polygons[1:]
            return poly, False

        return None

    def add_polygon(self, polygon, safe):
        assert len(polygon.exterior.coords) >= 3, "Must supply at least 3 points"
        # Splitting the polygon immediately, the result may be smaller than
        # what was input, but betther than failure
        polys = self.get_convex_poly(polygon)
        if safe:
            self.safe_polygons.extend(polys)
        else:
            self.bad_polygons.extend(polys)

    def get_convex_poly(self, complex_poly):
        # CCW polygon
        ccw_poly = orient(complex_poly, 1.0)
        convex_poly = ccw_poly.convex_hull
        # If concave (ie convex hull has less points), then split in triangles
        if len(list(ccw_poly.exterior.coords)) > len(list(convex_poly.exterior.coords)):
            return triangulate(complex_poly)
        else:
            return [complex_poly]
