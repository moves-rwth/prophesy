import numpy
from constraint_generation import ConstraintGeneration
from config import EPS
from data.constraint import Constraint
from sympy.polys.polytools import Poly
from shapely.geometry import LineString
from shapely.geometry.point import Point, asPoint

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
        # computes the bounding line orthogonal to the orientatation vector
        # returns None if no intersection or intersections are out of borders

        orthogonal_anchor = numpy.array(anchor) + orientation_vector
        orthogonal_vec = self.compute_orthogonal_vector(orientation_vector)

        # intersection with borders
        down = self.get_intersection(orthogonal_anchor, orthogonal_vec, numpy.array([0, 0]), numpy.array([1, 0]))
        left = self.get_intersection(orthogonal_anchor, orthogonal_vec, numpy.array([0, 0]), numpy.array([0, 1]))
        top = self.get_intersection(orthogonal_anchor, orthogonal_vec, numpy.array([0, 1]), numpy.array([1, 0]))
        right = self.get_intersection(orthogonal_anchor, orthogonal_vec, numpy.array([1, 0]), numpy.array([0, 1]))
        # print("\t\tBorders: {0}, {1}, {2}, {3}".format(down, left, top, right))
        bounds = []
        if down is not None and self.is_valid(down):
            bounds.append(down)
        if left is not None and self.is_valid(left):
            bounds.append(left)
        if top is not None and self.is_valid(top):
            bounds.append(top)
        if right is not None and self.is_valid(right):
            bounds.append(right)
        if len(bounds) != 2:
            return None
        else:
            return LineString(bounds)

    def is_valid(self, point):
        # checks if point is in rectangle [0,0] to [1,1]
        if (0 <= point.x and point.x <= 1):
            return (0 <= point.y and point.y <= 1)
        else:
            return False

    def rotate_vector(self, x, rad):
        R = numpy.matrix([[numpy.cos(rad), -numpy.sin(rad)], [numpy.sin(rad), numpy.cos(rad)]])
        result = x * R
        return numpy.array([result.item(0), result.item(1)])

    def normalize_vector(self, x):
        return x / numpy.linalg.norm(x)

    def get_intersection(self, anchor_a, vector_a, anchor_b, vector_b) :
        # computes intersection of two lines anchor_a + vector_a*x and anchor_b + vector_b*x
        # returns None if there is no intersection
        #TODO use intersection of lines
        dap = numpy.array([-vector_a[1], vector_a[0]])
        denom = numpy.dot( dap, vector_b)
        num = numpy.dot( dap, numpy.array(anchor_a) - numpy.array(anchor_b))
        if abs(denom) < EPS:
            return None
        else:
            return asPoint((num / denom) * vector_b + anchor_b)

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
        (best_bound1, best_bound2) = self.best_bounding

        # update anchor points
        self.anchor_points.append(best_bound1)
        self.anchor_points.append(best_bound2)
        #TODO only remove?
        self.remove_array(self.anchor_points, self.best_anchor)

        # remove additonal anchor points already in area
        for anchor in self.anchor_points:
            fullfillsAllConstraints = all([self.is_point_fulfilling_constraint(anchor, constraint) for constraint in new_constraints])
            if fullfillsAllConstraints:
                self.remove_array(self.anchor_points, anchor)
        print("anchor_points after: {0}".format(self.anchor_points))

        if self.max_area_safe:
            self.safe_planes.append(self.best_bounding)
        else:
            self.unsafe_planes.append(self.best_bounding)

        self.plot_results(additional_lines_green = self.safe_planes, additional_lines_red = self.unsafe_planes, additional_arrows = [(self.best_anchor, self.best_orientation_vector * self.best_dpt)], display = True)

    def next_constraint(self):
        # reset
        self.best_orientation_vector = numpy.array([1, 0])
        self.best_dpt = 0
        self.max_area_safe = False
        self.best_rad = None
        self.best_anchor = None
        self.max_size = 0
        self.best_line = None

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
                print("\t\tbounding line: {0}".format(line))
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

        (x1, y1, x2, y2) = self.best_line.bounds
        if (abs(x2 - x1) < EPS):
            # vertical line
            if (self.best_orientation_vector[0] > 0):
                rel = "<"
                neg_rel = ">="
            else:
                rel = ">="
                neg_rel = "<"
            new_constraint =  Constraint(Poly(self.parameters[0] - x1, self.parameters), rel, self.parameters)
            new_constraint_neg = Constraint(Poly(self.parameters[0] - x1, self.parameters), neg_rel, self.parameters)
            print("line is described by x = {0}".format(x1))

        else:
            # asserted x2 != x1
            # slope m = (y2-y1) / (x2-x1)
            m = (y2 - y1) / (x2 - x1)
            # two-point form
            #     y-y1 = m * (x-x1)
            # <=> 0 = mx - mx1 - y + y1
            # <=> 0 = mx - y + c with c = y1 - mx1
            c = y1 - m * x1

            # TODO correct?
            if (self.best_orientation_vector[0] > 0):
                # part left of line is in constraint
                rel = ">"
                neg_rel = "<="
            elif abs(self.best_orientation_vector[0]) < EPS and self.best_orientation_vector[1] > 0:
                # part below line is in constraint
                rel = ">"
                neg_rel = "<="
            else:
                rel = "<="
                neg_rel = ">"

            new_constraint = Constraint(Poly(m * self.parameters[0] - self.parameters[1] + c, self.parameters), rel, self.parameters)
            new_constraint_neg = Constraint(Poly(m * self.parameters[0] - self.parameters[1] + c, self.parameters), neg_rel, self.parameters)
            print("line is described by {m}x - y + {c} = 0".format(m = m, c = c))

        # new constraints + negation of previous constraints
        print("constraint: {0}".format(new_constraint))
        new_constraint_list = self.all_constraints_neg.copy()
        new_constraint_list.append(new_constraint)
        self.all_constraints_neg.append(new_constraint_neg)
        return (new_constraint_list, self.max_size, self.max_area_safe)
