import numpy
from constraint_generation import ConstraintGeneration, Anchor, Direction
from config import EPS
from shapely.geometry import LineString, MultiPoint, box
from shapely.geometry.point import Point
from shapely.geometry.polygon import Polygon
import sampling

class ConstraintPlanes(ConstraintGeneration):

    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc, _steps = 3):
        ConstraintGeneration.__init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc)
        self.steps = numpy.linspace(0, -(1 / 2 * numpy.pi), _steps, endpoint=False)

        self.safe_planes = []
        self.unsafe_planes = []

        self.anchor_points = []
        for pt, dir in [((0, 0), Direction.NE), ((1, 0), Direction.NW), ((1, 1), Direction.SW), ((0, 1), Direction.SE)]:
            value = self.ratfunc.eval({x:y for x,y in zip(self.parameters, pt)}).evalf()
            if (self.safe_above_threshold and value >= self.threshold) or (not self.safe_above_threshold and value < self.threshold):
                pt_safe = True
            else:
                pt_safe = False
            self.anchor_points.append(Anchor(Point(pt), dir, pt_safe))

        self.best_orientation_vector = None
        self.best_dpt = 0
        self.max_area_safe = False
        self.best_anchor = None
        self.best_plane = None
        self.best_line = None

    def compute_distance(self, point, anchor, orientation_vector):
        # returns distance between point and line with anchor and orientation_vector
        # see https://en.wikipedia.org/wiki/Distance_from_a_point_to_a_line#Vector_formulation
        difference = numpy.array(anchor)-numpy.array(point)
        tmp = difference - difference.dot(orientation_vector) * orientation_vector
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
        # print("\t\torthogonal: {0}".format(orthogonal_vec))

        for k in safe_samples.keys():
            dist = self.compute_distance(anchor_point, k, orthogonal_vec)
            if abs(dist) < abs(min_safe_dist):
                min_safe_dist = dist
        for k in bad_samples.keys():
            dist = self.compute_distance(anchor_point, k, orthogonal_vec)
            if abs(dist) < abs(min_bad_dist):
                min_bad_dist = dist

        # print("\t\tmin_safe_dist: {0}".format(min_safe_dist))
        # print("\t\tmin_bad_dist: {0}".format(min_bad_dist))

        if abs(min_safe_dist) == abs(min_bad_dist):
            return (True, 0)
        elif abs(min_safe_dist) < abs(min_bad_dist):
            # safe area
            return (True, min_bad_dist-EPS)
        else:
            # unsafe area
            assert(abs(min_safe_dist) > abs(min_bad_dist))
            return (False, min_safe_dist-EPS)

    def create_bounding_line(self, anchor, orientation_vector):
        """computes the bounding line orthogonal to the orientation vector"""
        bbox = box(0, 0, 1, 1)

        orthogonal_anchor = numpy.array(anchor) + orientation_vector
        orthogonal_vec = self.compute_orthogonal_vector(orientation_vector)

        # Ensure start and end are far enough outside of bbox to ensure intersection
        # compute_orthogonal_vector returns CW rotation
        start = Point(orthogonal_anchor + self.normalize_vector(orthogonal_vec)*2)
        end = Point(orthogonal_anchor - self.normalize_vector(orthogonal_vec)*2)
        line = LineString([start, end])

        intersections = line.intersection(bbox.boundary)
        if intersections is None or not isinstance(intersections, MultiPoint) or len(intersections) != 2:
            return None

        return LineString([intersections[0], intersections[1]])

    def create_plane(self, anchor, bounding_line):
        """computes the plane created by splitting along the bounding line
        with the anchor point in it
        the bounding line is orthogonal to the orientation vector"""
        (bound1, bound2) = bounding_line.coords
        int1 = Point(bound1)
        int2 = Point(bound2)

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
        and traversing the bounding box until end point is reached"""
        result = [(start.x, start.y)]
        corner_current = self.get_next_corner(start)
        corner_end = self.get_next_corner(end)
        while not corner_current.equals(corner_end):
            result.append((corner_current.x, corner_current.y))
            corner_current = self.get_next_corner(corner_current)
        result.append((end.x, end.y))
        return Polygon(result)

    def get_next_corner(self, point):
        """return the next corner point (CCW) for a point lying on the bounding box"""
        if point.x == 0:
            if point.y == 0:
                return Point(1, 0)
            else:
                return Point(0, 0)
        elif point.x == 1:
            if point.y == 1:
                return Point(0, 1)
            else:
                return Point(1, 1)
        elif point.y == 0:
            return Point(1, 0)
        else:
            assert(point.y == 1)
            return Point(0, 1)

    def rotate_vector(self, x, rad):
        R = numpy.matrix([[numpy.cos(rad), -numpy.sin(rad)], [numpy.sin(rad), numpy.cos(rad)]])
        result = x * R
        return numpy.array([result.item(0), result.item(1)])

    def normalize_vector(self, x):
        return x / numpy.linalg.norm(x)

    def fail_constraint(self, constraint, safe):
        if self.best_dpt < 0.05:
            return None
        self.best_dpt *= 0.5
        line = self.create_bounding_line(self.best_anchor.pos, self.best_orientation_vector*self.best_dpt)
        if line is None:
            return None
        self.best_line = line
        plane = self.create_plane(self.best_anchor.pos, self.best_line)
        if plane is None:
            return None
        self.best_plane = plane
        return (self.compute_constraint(self.best_plane), self.best_plane, self.max_area_safe)

    def reject_constraint(self, constraint, safe, sample):
        pass

    def accept_constraint(self, constraint, safe):
        (best_bound1, best_bound2) = self.best_line.coords
        best_bound1 = Point(best_bound1)
        best_bound2 = Point(best_bound2)
        safe = self.max_area_safe

        # Remove additional anchor points already in area
        anchors = self.anchor_points[:]
        for anchor in anchors:
            if self.is_point_fulfilling_constraint(list(anchor.pos.coords)[0], constraint):
                self.anchor_points.remove(anchor)

        # Add new anchors
        # First add possible anchors for first bound point
        if best_bound1.y == 0:
            self.anchor_points.append(Anchor(Point(best_bound1), Direction.NE, safe))
            if best_bound2.x > best_bound1.x:
                self.anchor_points.append(Anchor(Point(best_bound1), Direction.NW, safe))
        elif best_bound1.y == 1:
            self.anchor_points.append(Anchor(Point(best_bound1), Direction.SW, safe))
            if best_bound2.x < best_bound1.x:
                self.anchor_points.append(Anchor(Point(best_bound1), Direction.SE, safe))
        elif best_bound1.x == 0:
            self.anchor_points.append(Anchor(Point(best_bound1), Direction.SE, safe))
            if best_bound2.y > best_bound1.y:
                self.anchor_points.append(Anchor(Point(best_bound1), Direction.NE, safe))
        else:
            assert best_bound1.x == 1
            self.anchor_points.append(Anchor(Point(best_bound1), Direction.NW, safe))
            if best_bound2.y < best_bound1.y:
                self.anchor_points.append(Anchor(Point(best_bound1), Direction.SW, safe))

        # Then for second bound point. Constraint is now on other side of the line
        if best_bound2.y == 0:
            self.anchor_points.append(Anchor(Point(best_bound2), Direction.NW, safe))
            if best_bound1.x > best_bound2.x:
                self.anchor_points.append(Anchor(Point(best_bound2), Direction.NE, safe))
        elif best_bound2.y == 1:
            self.anchor_points.append(Anchor(Point(best_bound2), Direction.SE, safe))
            if best_bound1.x < best_bound2.x:
                self.anchor_points.append(Anchor(Point(best_bound2), Direction.SW, safe))
        elif best_bound2.x == 0:
            self.anchor_points.append(Anchor(Point(best_bound2), Direction.NE, safe))
            if best_bound1.y > best_bound2.y:
                self.anchor_points.append(Anchor(Point(best_bound2), Direction.SE, safe))
        else:
            assert best_bound2.x == 1
            self.anchor_points.append(Anchor(Point(best_bound2), Direction.SW, safe))
            if best_bound1.y < best_bound2.y:
                self.anchor_points.append(Anchor(Point(best_bound2), Direction.NW, safe))

        if self.max_area_safe:
            self.safe_planes.append(self.best_plane)
        else:
            self.unsafe_planes.append(self.best_plane)

    def next_constraint(self):
        # reset
        self.best_orientation_vector = numpy.array([1, 0])
        self.best_dpt = 0
        self.max_area_safe = False
        self.best_anchor = None
        self.best_plane = None
        self.best_line = None

        # split samples into safe and bad
        (safe_samples, bad_samples) = sampling.split_samples(self.samples, self.threshold, self.safe_above_threshold)

        for anchor in self.anchor_points:
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

                line = self.create_bounding_line(anchor.pos, orientation_vector*dpt)
                if line is None:
                    continue

                plane = self.create_plane(anchor.pos, line)
                if plane is None:
                    continue

                # check for intersection with existing planes
                # TODO make more efficient
                for plane2 in self.safe_planes if area_safe else self.unsafe_planes:
                    if (self.intersects(plane, plane2)):
                        plane = plane.difference(plane2)
                        #print("After intersection: {}".format(plane))
                        #self.plot_results(poly_blue = [plane, plane2], display=True)

                #orientation_line = LineString([anchor.pos, Point(numpy.array(anchor.pos) + orientation_vector*dpt)])
                #self.plot_results(anchor_points=self.anchor_points, poly_blue = [plane], additional_arrows = [orientation_line], display=True)

                # choose best
                if self.best_plane is None or (plane.area > self.best_plane.area and plane.area > self.threshold_area):
                    self.best_orientation_vector = orientation_vector
                    self.best_dpt = dpt
                    self.max_area_safe = area_safe
                    self.best_anchor = anchor
                    self.best_plane = plane
                    self.best_line = line

        if self.best_plane is None:
            return None

        return (self.compute_constraint(self.best_plane), self.best_plane, self.max_area_safe)
