import numpy
from constraint_generation import ConstraintGeneration
from config import EPS
from data.constraint import Constraint
from sympy.polys.polytools import Poly
from shapely.geometry import LineString
from shapely.geometry.point import Point, asPoint
import sampling
from shapely.geometry.polygon import LinearRing
from shapely.geometry.multipoint import MultiPoint

class ConstraintPlanes(ConstraintGeneration):

    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc, _steps = 3):
        ConstraintGeneration.__init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc)
        self.steps = _steps
        self.deg90 = 1 / 2 * numpy.pi;
        self.step_radius = -self.deg90 / self.steps

        self.safe_planes = []
        self.unsafe_planes = []

        self.anchor_points = [Point(0,0), Point(1,0), Point(1,1), Point(0,1)]
        self.best_orientation_vector = None
        self.best_dpt = 0
        self.max_area_safe = False
        self.max_size = 0
        self.best_rad = None
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
            return (True, min_bad_dist)
        else:
            # unsafe area
            assert(abs(min_safe_dist) > abs(min_bad_dist))
            return (False, min_safe_dist)

    def create_bounding_line(self, anchor, orientation_vector):
        """computes the bounding line orthogonal to the orientatation vector
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

    def remove_array(self, L, arr):
        ind = 0
        size = len(L)
        while ind != size and not numpy.array_equal(L[ind], arr):
            ind += 1
        if ind != size:
            L.pop(ind)
        else:
            raise ValueError('array not found in list.')

    def change_current_constraint(self):
        # TODO implement
        return

    def finalize_step(self, new_constraints):
        print("anchor_points before: {0}".format(self.anchor_points))
        (best_bound1, best_bound2) = self.best_line.coords

        # update anchor points
        self.anchor_points.append(Point(best_bound1))
        self.anchor_points.append(Point(best_bound2))
        #TODO only remove?
        self.remove_array(self.anchor_points, self.best_anchor)

        # remove additonal anchor points already in area
        for anchor in self.anchor_points:
            fullfillsAllConstraints = all([self.is_point_fulfilling_constraint(list(anchor.coords)[0], constraint) for constraint in new_constraints])
            if fullfillsAllConstraints:
                self.remove_array(self.anchor_points, anchor)
        print("anchor_points after: {0}".format(self.anchor_points))

        if self.max_area_safe:
            self.safe_planes.append(self.best_line)
        else:
            self.unsafe_planes.append(self.best_line)

        self.plot_results(additional_lines_green = self.safe_planes, additional_lines_red = self.unsafe_planes, additional_arrows = [LineString([self.best_anchor, self.best_orientation_vector * self.best_dpt])], display = True)

    def next_constraint(self):
        # reset
        self.best_orientation_vector = numpy.array([1, 0])
        self.best_dpt = 0
        self.max_area_safe = False
        self.best_rad = None
        self.best_anchor = None
        self.max_size = 0
        self.best_line = None

        # split samples into safe and bad
        (self.safe_samples, self.bad_samples) = sampling.split_samples(self.samples, self.threshold, self.safe_above_threshold)
        assert(len(self.safe_samples) + len(self.bad_samples) == len(self.samples))

        for anchor in self.anchor_points:
            print("anchor: {0}".format(anchor))
            for i in range(0, self.steps):
                # orientation vector according to 90°/steps
                degree = i * self.step_radius
                orientation_vector = self.normalize_vector(self.rotate_vector(numpy.array([1, 0]), degree))
                print("\to-vec: {0}".format(orientation_vector))

                (area_safe, dpt) = self.create_halfspace_depth(self.safe_samples, self.bad_samples, anchor, orientation_vector)
                if abs(dpt) < EPS:
                    continue
                line = self.create_bounding_line(anchor, orientation_vector*dpt)
                if line is None:
                    continue
                print("\t\tbounding line: {0} {1} {2}".format(line, area_safe, dpt))
                point2 = anchor + orientation_vector * dpt
                anchor_line = LineString([anchor, point2])
                self.plot_results(additional_lines_blue = [line], additional_arrows = [anchor_line], display=False)
                # chooose best
                if dpt > self.best_dpt:
                    self.best_orientation_vector = orientation_vector
                    self.best_dpt = dpt
                    self.max_area_safe = area_safe
                    self.best_rad = degree
                    self.best_anchor = anchor
                    self.best_line = line
                    #TODO compute maximal size
                    self.max_size = 0

        if self.best_line is None:
            return None

        print("Best orientation: {0}".format(self.best_orientation_vector))
        print("Best distance: {0}".format(self.best_dpt))
        print("Best area: {0}".format(self.max_area_safe))
        print("Best anchor: {0}".format(self.best_anchor))
        print("Best bounds: {0}".format(self.best_line))
        point2 = self.best_anchor + self.best_orientation_vector * self.best_dpt
        anchor_line = LineString([self.best_anchor, point2])
        self.plot_results(additional_lines_blue = [self.best_line], additional_arrows = [anchor_line], display=True)

        return (self.compute_constraint(self.best_line), self.best_line, self.max_area_safe)
