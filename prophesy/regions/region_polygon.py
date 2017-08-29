from shapely.ops import triangulate
from shapely.geometry.polygon import orient

from prophesy.regions.region_generation import RegionGenerator
from prophesy.regions.welldefinedness import check_welldefinedness, WelldefinednessResult


class ConstraintPolygon(RegionGenerator):
    """
    This generator is meant to be used via a user interface, as it cannot generate new polygons itself.
    Moreover, this generator is limited to 2 dimensions.
    """

    def __init__(self, samples, parameters, threshold, _smt2interface, wd_constraints, gp_constraints):
        if len(parameters) != 2:
            raise NotImplementedError

        RegionGenerator.__init__(self, samples, parameters, threshold, _smt2interface, wd_constraints, gp_constraints)

        self.safe_polygons = []
        self.bad_polygons = []

    def fail_region(self):
        # TODO inform user
        # TODO: convex constraint might be split in triangles
        return None

    def accept_region(self):
        pass

    def reject_region(self, sample):
        pass

    def ignore_region(self):
        pass

    def next_region(self):
        if len(self.safe_polygons) > 0:
            poly = self.safe_polygons[0]
            self.safe_polygons = self.safe_polygons[1:]
            # TODO check that the polygons are indeed welldefined.
            return poly, WelldefinednessResult.Welldefined, True
        elif len(self.bad_polygons) > 0:
            poly = self.bad_polygons[0]
            self.bad_polygons = self.bad_polygons[1:]
            # TODO check that the polygons are indeed welldefined.
            return poly, WelldefinednessResult.Welldefined, False

        return None

    def add_polygon(self, polygon, safe):
        """
        Add new polygon.
        :param polygon: Polygon.
        :param safe: Flag iff the polygon should be considered safe.
        """
        assert len(polygon.exterior.coords) >= 3, "Must supply at least 3 points"
        # Splitting the polygon immediately, the result may be smaller than what was input, but better than failure
        polys = self._get_convex_poly(polygon)
        if safe:
            self.safe_polygons.extend(polys)
        else:
            self.bad_polygons.extend(polys)

    def _get_convex_poly(self, complex_poly):
        """
        Makes polynomial convex.
        :param complex_poly: Polygon.
        :return: List of convex polygons.
        """
        # CCW polygon
        ccw_poly = orient(complex_poly, 1.0)
        convex_poly = ccw_poly.convex_hull
        # If concave (i.e., convex hull has less points), then split in triangles
        if len(list(ccw_poly.exterior.coords)) > len(list(convex_poly.exterior.coords)):
            return triangulate(complex_poly)
        else:
            return [complex_poly]

    def plot_candidate(self):
        if len(self.safe_polygons) > 0:
            poly = self.safe_polygons[0]
            self.plot_results(poly_blue_dotted=[poly], display=False)
        elif len(self.bad_polygons) > 0:
            poly = self.bad_polygons[0]
            self.plot_results(poly_blue_crossed=[poly], display=False)
