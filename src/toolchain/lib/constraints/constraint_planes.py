import numpy
from constraint_generation import ConstraintGeneration, Anchor, Direction
from config import EPS
from shapely.geometry import LineString
from shapely.geometry.point import Point
from shapely.geometry.polygon import LinearRing, Polygon
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
        self.best_line = None
        self.all_constraints_neg = []

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
        """computes the bounding line orthogonal to the orientation vector
        Ensures area of the line is at the RHS
        returns None if no intersection or intersections are out of borders"""
        bbox = LinearRing([(0,0),(1,0),(1,1),(0,1)])

        orthogonal_anchor = numpy.array(anchor) + orientation_vector
        orthogonal_vec = self.compute_orthogonal_vector(orientation_vector)

        if not (0 <= orthogonal_anchor[0] <= 1) or not (0 <= orthogonal_anchor[1] <= 1):
            # Line outside of bbox
            return None

        # Ensure start and end are far enough outside of bbox to ensure intersection
        p = Point(orthogonal_anchor)
        # First + then - ensures RHS of line is constraint area
        # compute_orthogonal_vector returns CW rotation
        start = Point(orthogonal_anchor + self.normalize_vector(orthogonal_vec)*2)
        end = Point(orthogonal_anchor - self.normalize_vector(orthogonal_vec)*2)

        line1 = LineString([start, p])
        line2 = LineString([p, end])
        intersection1 = line1.intersection(bbox)
        intersection2 = line2.intersection(bbox)
        if intersection1 is None or intersection2 is None:
            return None
        if not isinstance(intersection1, Point) or not isinstance(intersection2, Point):
            # Each intersection must be a single point
            return None
        return LineString((intersection1, intersection2))

    def rotate_vector(self, x, rad):
        R = numpy.matrix([[numpy.cos(rad), -numpy.sin(rad)], [numpy.sin(rad), numpy.cos(rad)]])
        result = x * R
        return numpy.array([result.item(0), result.item(1)])

    def normalize_vector(self, x):
        return x / numpy.linalg.norm(x)

    def get_area_poly(self, anchor, line):
        return Polygon(list(anchor.pos.coords) + list(line.coords))

    def plot_candidate(self):
        point2 = self.best_anchor.pos + self.best_orientation_vector * self.best_dpt
        anchor_line = LineString([self.best_anchor.pos, point2])
        self.plot_results(anchor_points=self.anchor_points, poly_blue = [self.best_line], additional_arrows = [anchor_line], display=False)

    def fail_constraint(self, constraint, safe):
        if self.best_dpt < 0.05:
            return None
        self.best_dpt *= 0.5
        line = self.create_bounding_line(self.best_anchor.pos, self.best_orientation_vector*self.best_dpt)
        if line is None:
            return None
        self.best_line = line
        area_poly = self.get_area_poly(self.best_anchor, line)
        return (self.compute_constraint(self.best_line), area_poly, self.max_area_safe)

    def reject_constraint(self, constraint, safe, sample):
        pass

    def accept_constraint(self, constraint, safe):
        (best_bound1, best_bound2) = self.best_line.coords
        best_bound1 = Point(best_bound1)
        best_bound2 = Point(best_bound2)

        # Remove additional anchor points already in area
        anchors = self.anchor_points[:]
        for anchor in anchors:
            if self.is_point_fulfilling_constraint(list(anchor.pos.coords)[0], constraint):
                self.anchor_points.remove(anchor)

        # Add new anchors
        # First add possible anchors for first bound point
        if best_bound1.y == 0:
            self.anchor_points.append(Anchor(Point(best_bound1), Direction.NE))
            if best_bound2.x > best_bound1.x:
                self.anchor_points.append(Anchor(Point(best_bound1), Direction.NW))
        elif best_bound1.y == 1:
            self.anchor_points.append(Anchor(Point(best_bound1), Direction.SW))
            if best_bound2.x < best_bound1.x:
                self.anchor_points.append(Anchor(Point(best_bound1), Direction.SE))
        elif best_bound1.x == 0:
            self.anchor_points.append(Anchor(Point(best_bound1), Direction.SE))
            if best_bound2.y > best_bound1.y:
                self.anchor_points.append(Anchor(Point(best_bound1), Direction.NE))
        else:
            assert best_bound1.x == 1
            self.anchor_points.append(Anchor(Point(best_bound1), Direction.NW))
            if best_bound2.y < best_bound1.y:
                self.anchor_points.append(Anchor(Point(best_bound1), Direction.SW))

        # Then for second bound point. Constraint is now on other side of the line
        if best_bound2.y == 0:
            self.anchor_points.append(Anchor(Point(best_bound2), Direction.NW))
            if best_bound1.x > best_bound2.x:
                self.anchor_points.append(Anchor(Point(best_bound2), Direction.NE))
        elif best_bound2.y == 1:
            self.anchor_points.append(Anchor(Point(best_bound2), Direction.SE))
            if best_bound1.x < best_bound2.x:
                self.anchor_points.append(Anchor(Point(best_bound2), Direction.SW))
        elif best_bound2.x == 0:
            self.anchor_points.append(Anchor(Point(best_bound2), Direction.NE))
            if best_bound1.y > best_bound2.y:
                self.anchor_points.append(Anchor(Point(best_bound2), Direction.SE))
        else:
            assert best_bound2.x == 1
            self.anchor_points.append(Anchor(Point(best_bound2), Direction.SW))
            if best_bound1.y < best_bound2.y:
                self.anchor_points.append(Anchor(Point(best_bound2), Direction.NW))

        if self.max_area_safe:
            self.safe_planes.append(self.best_line)
        else:
            self.unsafe_planes.append(self.best_line)

    def next_constraint(self):
        # reset
        self.best_orientation_vector = numpy.array([1, 0])
        self.best_dpt = 0
        self.max_area_safe = False
        self.best_anchor = None
        self.best_line = None
        
        best_area_poly = None

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

                area_poly = self.get_area_poly(anchor, line)

                # choose best
                if best_area_poly is None or area_poly.area > best_area_poly.area:
                    self.best_orientation_vector = orientation_vector
                    self.best_dpt = dpt
                    self.max_area_safe = area_safe
                    self.best_anchor = anchor
                    self.best_line = line
                    best_area_poly = area_poly

        if self.best_line is None:
            return None

        return (self.compute_constraint(self.best_line), best_area_poly, self.max_area_safe)
