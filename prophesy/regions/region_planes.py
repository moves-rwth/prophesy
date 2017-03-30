from prophesy.data.samples import SamplePoint
from prophesy.regions.region_generation import RegionGenerator
from prophesy.regions.region_rectangles import Anchor, Direction
from prophesy.config import configuration
from shapely.geometry import LineString, MultiPoint, box
from shapely.geometry.polygon import Polygon
import numpy
import shapely.geometry.point
import prophesy.data.point

#TODO: Effect of this?
EPS = 0.00125

class ConstraintPlanes(RegionGenerator):

    def __init__(self, samples, parameters, threshold, threshold_area, _smt2interface, _ratfunc, _steps=3):
        assert len(parameters) == 2, "Planes can be constructed in 2 dim only"
        RegionGenerator.__init__(self, samples, parameters, threshold, threshold_area, _smt2interface, _ratfunc)
        self.steps = numpy.linspace(0, -(1 / 2 * numpy.pi), _steps, endpoint=False)

        self.x_min = parameters[0].interval.left_bound()
        self.x_max = parameters[0].interval.right_bound()
        self.y_min = parameters[1].interval.left_bound()
        self.y_max = parameters[1].interval.right_bound()

        #TODO: safe/unsafe also stored in base class
        self.safe_planes = []
        self.unsafe_planes = []

        self.anchor_points = []

        # Add anchors CCW
        for pt, direction in [
                ((self.x_min, self.y_min), Direction.NE),
                ((self.x_max, self.y_min), Direction.NW),
                ((self.x_max, self.y_max), Direction.SW),
                ((self.x_min, self.y_max), Direction.SE)]:
            # initialy safe flag for anchors properly
            sp = SamplePoint.from_point(prophesy.data.point.Point(*pt), self.parameters.get_variable_order())
            value = self.ratfunc.eval(sp)
            if value >= self.threshold:
                pt_safe = True
            else:
                pt_safe = False
            self.anchor_points.append(Anchor(shapely.geometry.point.Point(pt), direction, pt_safe))

        self.best_orientation_vector = None
        self.best_dpt = 0
        self.max_area_safe = False
        self.best_anchor = None
        self.best_plane = None

    def compute_distance(self, point, anchor, orientation_vector):
        # returns distance between point and line with anchor and orientation_vector
        # see https://en.wikipedia.org/wiki/Distance_from_a_point_to_a_line#Vector_formulation
        difference = numpy.array(anchor) - numpy.array(point)
        # Operator order matters asnumpy is involed i.c.w. pycarl
        tmp = difference - orientation_vector * difference.dot(orientation_vector)
        distance = numpy.array([numpy.float64(tmp.item(0)), numpy.float64(tmp.item(1))])
        return numpy.linalg.norm(distance)

    def compute_orthogonal_vector(self, vector):
        # computes one of the orthogonal vectors to vector
        # Rotates CW
        return numpy.array([vector.item(1), -vector.item(0)])

    def create_halfspace_depth(self, safe_samples, bad_samples, anchor_point, orientation_vector):
        assert(numpy.linalg.norm(orientation_vector) == 1)

        # compute minimal/maximal safe/bad distances
        min_safe_dist = 1000
        min_bad_dist = 1000

        orthogonal_vec = self.compute_orthogonal_vector(orientation_vector)

        for k in safe_samples.keys():
            dist = self.compute_distance(anchor_point, k, orthogonal_vec)
            if abs(dist) < abs(min_safe_dist):
                min_safe_dist = dist
        for k in bad_samples.keys():
            dist = self.compute_distance(anchor_point, k, orthogonal_vec)
            if abs(dist) < abs(min_bad_dist):
                min_bad_dist = dist

        if abs(min_safe_dist) == abs(min_bad_dist):
            return True, 0
        elif abs(min_safe_dist) < abs(min_bad_dist):
            # safe area
            return True, min_bad_dist - configuration.get_regions_precision()
        else:
            # unsafe area
            assert(abs(min_safe_dist) > abs(min_bad_dist))
            return False, min_safe_dist - configuration.get_regions_precision()

    def create_plane(self, anchor, orientation_vector):
        """computes the plane created by splitting along the bounding line
        with the anchor point in it
        the bounding line is orthogonal to the orientation vector
        @param anchor shapely Point
        @param orientation_vector 2D numpy.array
        @return shapely Polygon
        """
        bbox = box(self.x_min, self.y_min, self.x_max, self.y_max)

        orthogonal_anchor = numpy.array(anchor) + orientation_vector
        orthogonal_vec = self.compute_orthogonal_vector(orientation_vector)

        # Ensure start and end of bounding line are far enough outside of bbox to ensure intersection
        # compute_orthogonal_vector returns CW rotation
        start = shapely.geometry.point.Point(orthogonal_anchor + self.normalize_vector(orthogonal_vec)*2)
        end = shapely.geometry.point.Point(orthogonal_anchor - self.normalize_vector(orthogonal_vec)*2)
        bounding_line = LineString([start, end])

        intersections = bounding_line.intersection(bbox.boundary)
        if intersections is None or not isinstance(intersections, MultiPoint) or len(intersections) != 2:
            return None

        int1 = intersections[0]
        int2 = intersections[1]

        half_A = self.get_halfspace_polygon(int1, int2)
        half_B = self.get_halfspace_polygon(int2, int1)

        if self.is_inside_polygon(anchor, half_A):
            plane = half_A
        elif self.is_inside_polygon(anchor, half_B):
            plane = half_B
        else:
            return None

        return plane

    def get_halfspace_polygon(self, start, end):
        """compute a halfspace polygon starting at poin start
        and traversing the bounding box until end point is reached
        @param start shapely.geometry.point.Point
        @param end shapely.geometry.point.Point
        @result shapely Polygon
        """
        result = [(start.x, start.y)]
        corner_current = self.get_next_corner(start)
        corner_end = self.get_next_corner(end)
        while not corner_current.equals(corner_end):
            result.append((corner_current.x, corner_current.y))
            corner_current = self.get_next_corner(corner_current)
        result.append((end.x, end.y))
        return Polygon(result)

    def get_next_corner(self, point):
        """Return the next corner point (CCW) for a point lying on the bounding
        box. The result is a shapely Point
        @param point shapely.geometry.point.Point
        @return shapely.geometry.point.Point
        """
        if point.x == self.x_min:
            if point.y == self.y_min:
                return shapely.geometry.point.Point(self.x_max, self.y_min)
            else:
                return shapely.geometry.point.Point(self.x_min, self.y_min)
        elif point.x == self.x_max:
            if point.y == self.y_max:
                return shapely.geometry.point.Point(self.x_min, self.y_max)
            else:
                return shapely.geometry.point.Point(self.x_max, self.y_max)
        elif point.y == self.y_min:
            return shapely.geometry.point.Point(self.x_max, self.y_min)
        else:
            assert(point.y == self.y_max)
            return shapely.geometry.point.Point(self.x_min, self.y_max)

    def rotate_vector(self, x, rad):
        R = numpy.matrix([[numpy.cos(rad), -numpy.sin(rad)], [numpy.sin(rad), numpy.cos(rad)]])
        result = x * R
        return numpy.array([result.item(0), result.item(1)])

    def normalize_vector(self, x):
        return x / numpy.linalg.norm(x)

    def is_valid_orientation(self, anchor, direction):
        """Tests if anchor and direction are valid as new anchor
        @param anchor shapely Point
        @param direction 2D numpy.array
        """
        # Testing if point with small distance from anchor in direction is in unknown area
        offset_coords = numpy.array(anchor) + direction * EPS * 2
        point_test = shapely.geometry.point.Point(offset_coords)

        if point_test.x < self.x_min or point_test.x > self.x_max or \
                point_test.y < self.y_min or point_test.y> self.y_max:
            return False

        for plane in self.safe_planes + self.unsafe_planes:
            if self.is_inside_polygon(point_test, plane):
                return False
        return True

    def refine_with_intersections(self, polygon):
        """Given the plane as argument, cut away known areas.
        """
        # check for intersection with existing planes
        # TODO make more efficient
        for plane2 in self.safe_planes + self.unsafe_planes:
            if self.intersects(polygon, plane2):
                polygon = polygon.difference(plane2)
        return polygon

    def plot_candidate(self):
        orientation_line = LineString([self.best_anchor.pos, shapely.geometry.point.Point(numpy.array(self.best_anchor.pos) + self.best_orientation_vector * self.best_dpt)])
        self.plot_results(anchor_points=self.anchor_points, poly_blue=[self.best_plane], additional_arrows=[orientation_line], display=True)

    def fail_constraint(self, constraint, safe):
        if self.best_dpt < EPS:
            return None
        self.best_dpt *= 0.5
        plane = self.create_plane(self.best_anchor.pos, self.best_orientation_vector * self.best_dpt)
        if plane is None:
            return None
        plane = self.refine_with_intersections(plane)
        if plane is None:
            return None

        if plane.area < self.threshold_area:
            return None

        self.best_plane = plane
        return self.best_plane, self.max_area_safe

    def reject_constraint(self, constraint, safe, sample):
        pass

    def accept_constraint(self, constraint, safe):
        assert(self.max_area_safe == safe)
        if self.max_area_safe:
            self.safe_planes.append(self.best_plane)
        else:
            self.unsafe_planes.append(self.best_plane)

        # Remove additional anchor points already in area
        anchors = self.anchor_points[:]
        for anchor in anchors:
            if self.is_inside_polygon(anchor.pos, constraint):
                self.anchor_points.remove(anchor)

        for point in self.best_plane.boundary.coords:
            # Test all directions for anchor
            point = shapely.geometry.point.Point(point)
            for direction in [Direction.NE, Direction.NW, Direction.SW, Direction.SE]:
                if self.is_valid_orientation(point, direction.to_vector()):
                    self.anchor_points.append(Anchor(point, direction, safe))
        #self.plot_results(anchor_points=self.anchor_points, display=True)

    def next_constraint(self):
        # reset
        self.best_orientation_vector = numpy.array([1, 0])
        self.best_dpt = 0
        self.max_area_safe = False
        self.best_anchor = None
        self.best_plane = None

        # split samples into safe and bad
        (safe_samples, bad_samples) = self.samples.split(self.threshold)

        for anchor in self.anchor_points:
            #TODO: use anchor.to_vector. Have steps start in negative direction
            # (as direction lies halfway).
            # Normalize the vector return by to_vector, either here or there
            orientation = {
                      Direction.NE: numpy.array([1, 0]),
                      Direction.NW: numpy.array([0, 1]),
                      Direction.SW: numpy.array([-1, 0]),
                      Direction.SE: numpy.array([0, -1])}[anchor.dir]
            for step in self.steps:
                # orientation vector according to 90°/steps
                orientation_vector = self.normalize_vector(self.rotate_vector(orientation, step))

                (area_safe, dpt) = self.create_halfspace_depth(safe_samples, bad_samples, anchor.pos, orientation_vector)
                if abs(dpt) < EPS:
                    continue

                plane = self.create_plane(anchor.pos, orientation_vector * dpt)
                if plane is None:
                    continue

                plane = self.refine_with_intersections(plane)
                if plane is None:
                    continue

                #orientation_line = LineString([anchor.pos, Point(numpy.array(anchor.pos) + orientation_vector*dpt)])
                #self.plot_results(anchor_points=self.anchor_points, poly_blue = [plane], additional_arrows = [orientation_line], display=True)

                # choose best
                if self.best_plane is None or (plane.area > self.best_plane.area and plane.area > self.threshold_area):
                    # check if nothing of other polarity is inbetween.
                    other_points = bad_samples.keys() if area_safe else safe_samples.keys()
                    break_attempt = False
                    for point2 in other_points:
                        point2 = shapely.geometry.point.Point(point2)
                        if self.is_inside_polygon(point2, plane):
                            # wrong sample in covered area
                            break_attempt = True
                            break

                    if not break_attempt:
                        self.best_orientation_vector = orientation_vector
                        self.best_dpt = dpt
                        self.max_area_safe = area_safe
                        self.best_anchor = anchor
                        self.best_plane = plane

        if self.best_plane is None:
            return None

        return self.best_plane, self.max_area_safe

    def plot_results(self, *args, **kwargs):
        if not self.plot:
            return
        kwargs['anchor_points'] = self.anchor_points
        super().plot_results(*args, **kwargs)
