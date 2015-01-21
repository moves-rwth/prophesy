from constraint_generation import *

import numpy as np
from numpy import cos, sin
import sympy

class ConstraintPlanes(ConstraintGeneration):
    
    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc, _steps=3):
        ConstraintGeneration.__init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc)
        self.steps = _steps
        self.deg90 = 1/2 * np.pi;
        self.step_radius = -self.deg90/self.steps

        self.anchor_points = [np.array([0,0]), np.array([1,0]), np.array([1,1]), np.array([0,1])]
        self.best_orientation_vector = None
        self.best_dpt = 0
        self.max_area_safe = False
        self.max_size = 0
        self.best_rad = None
        self.best_anchor = None
        self.best_bounding = None

    def compute_distance(self, point, anchor, orientation_vector):
        # returns distance between point and line with anchor and orientation_vector
        # see https://en.wikipedia.org/wiki/Distance_from_a_point_to_a_line#Vector_formulation
        difference = anchor-point
        tmp = difference - difference.dot(orientation_vector) * orientation_vector
        distance = np.array([np.float64(tmp.item(0)), np.float64(tmp.item(1))])
        return np.linalg.norm(distance)

    def compute_orthogonal_vector(self, vector):
        # computes one of the orthogonal vectors to vector
        return np.array([vector.item(1), -vector.item(0)])

    def create_halfspace_depth(self, safe_samples, bad_samples, anchor_point, orientation_vector):
        assert(np.linalg.norm(orientation_vector) == 1)

        # compute minimal/maximal safe/bad distances
        min_safe_dist = 1000
        min_bad_dist = 1000
        max_safe_dist = 0
        max_bad_dist = 0

        orthogonal_vec = self.compute_orthogonal_vector(orientation_vector)
        print("\t\torthogonal: {0}".format(orthogonal_vec))

        for k,v in safe_samples.items():
            dist = self.compute_distance(anchor_point, k, orthogonal_vec)
            weighted_dist = dist
            #weighted_dist = np.dot(k - anchor_point, orientation_vector)
            if abs(weighted_dist) < abs(min_safe_dist):
                min_safe_dist = weighted_dist
            if abs(weighted_dist) > abs(max_safe_dist):
                max_safe_dist = weighted_dist
        for k,v in bad_samples.items():
            dist = self.compute_distance(anchor_point, k, orthogonal_vec)
            weighted_dist = dist
            #weighted_dist = np.dot(k - anchor_point, orientation_vector)
            if abs(weighted_dist) < abs(min_bad_dist):
                min_bad_dist = weighted_dist
            if abs(weighted_dist) > abs(max_bad_dist):
                max_bad_dist = weighted_dist

        if abs(min_safe_dist) == abs(min_bad_dist):
            return (True, 0)
        elif abs(min_safe_dist) < abs(min_bad_dist):
            safe = True
        else: 
            assert(abs(min_safe_dist) > abs(min_bad_dist))
            safe = False

        print("\t\tmin_safe_dist: {0}".format(min_safe_dist))
        print("\t\tmin_bad_dist: {0}".format(min_bad_dist))

        if safe:
            depth_pt = min_bad_dist
        else:
            depth_pt = min_safe_dist
        return (safe, depth_pt)

    def create_bounding_line(self, anchor, orientation_vector):
        # computes the bounding line orthogonal to the orientatation vector
        # returns two point composing the bounding line on borders
        # returns None if no intersection or intersections are out of borders

        print("\t\torientation: {0}".format(orientation_vector))
        orthogonal_anchor = anchor + orientation_vector
        orthogonal_vec = self.compute_orthogonal_vector(orientation_vector)
        print("\t\torthogonal anchor: {0}".format(orthogonal_anchor))
        print("\t\torthogonal vector: {0}".format(orthogonal_vec))

        # intersection with borders
        down = self.get_intersection(orthogonal_anchor, orthogonal_vec, np.array([0,0]), np.array([1,0]))
        left = self.get_intersection(orthogonal_anchor, orthogonal_vec, np.array([0,0]), np.array([0,1]))
        top = self.get_intersection(orthogonal_anchor, orthogonal_vec, np.array([0,1]), np.array([1,0]))
        right = self.get_intersection(orthogonal_anchor, orthogonal_vec, np.array([1,0]), np.array([0,1]))
        print("\t\tBorders: {0}, {1}, {2}, {3}".format(down, left, top, right))
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
            bound1 = bounds[0]
            bound2 = bounds[1]
            return (bound1, bound2)

    def is_valid(self, point):
        # checks if point is in rectangle [0,0] to [1,1]
        if (0 <= point[0] and point[0] <= 1):
            return (0 <= point[1] and point[1] <= 1)
        else:
            return False

    def rotate_vector(self, x, rad):
        R = np.matrix([[np.cos(rad), -np.sin(rad)],[np.sin(rad), np.cos(rad)]])
        result = x * R
        return np.array([result.item(0), result.item(1)])

    def normalize_vector(self, x):
        return x / np.linalg.norm(x)

    def get_intersection(self, anchor_a, vector_a, anchor_b, vector_b) :
        # computes intersection of two lines anchor_a + vector_a*x and anchor_b + vector_b*x
        # returns None if there is no intersection
        dap = np.array([-vector_a[1], vector_a[0]])
        denom = np.dot( dap, vector_b)
        num = np.dot( dap, anchor_a - anchor_b )
        if abs(denom) < EPS:
            return None
        else:
            return (num / denom) * vector_b + anchor_b

    def change_current_constraint(self):
        #TODO implement
        return

    def finalize_step(self):
        #TODO implement more
        result_bounding = self.create_bounding_line(self.best_anchor, self.best_orientation_vector*self.best_dpt)
        if result_bounding is not None:
            (bound1, bound2) = result_bounding
            print("bounding line: {0}, {1}".format(bound1, bound2))
            self.plot_results(additional_lines = [(bound1, bound2)], additional_arrows = [(self.best_anchor, self.best_orientation_vector*self.best_dpt)], name = "intermediate{0}".format(self.nr), display=False)

    def next_constraint(self):
        # reset
        self.best_orientation_vector = np.array([1, 0])
        self.best_dpt = 0
        self.max_area_safe = False
        self.best_rad = None
        self.best_anchor = None
        self.max_size = 0
        self.best_bounding = None

        for anchor in self.anchor_points:
            print("anchor: {0}".format(anchor))
            for i in range(0, self.steps):
                # orientation vector according to 90°/steps
                degree = i * self.step_radius
                orientation_vector = self.normalize_vector(self.rotate_vector(np.array([1,0]), degree))
                print("\to-vec: {0}".format(orientation_vector))

                (area_safe, dpt) =  self.create_halfspace_depth(self.safe_samples, self.bad_samples, anchor, orientation_vector)
                if abs(dpt) < EPS:
                    continue
                result_bounding = self.create_bounding_line(anchor, orientation_vector*dpt)
                if result_bounding is None:
                    continue
                (bound1, bound2) = result_bounding
                print("\t\tbounding line: {0}, {1}".format(bound1, bound2))
                self.plot_results(additional_lines = [(bound1, bound2)], additional_arrows = [(anchor, orientation_vector*dpt)], name = "call{0}".format(self.nr), display=False, first = (self.nr == 1))
                self.nr += 1
                # chooose best
                if dpt > self.best_dpt:
                    self.best_orientation_vector = orientation_vector
                    self.best_dpt = dpt
                    self.max_area_safe = area_safe
                    self.best_rad = degree
                    self.best_anchor = anchor
                    self.best_bounding = (bound1, bound2)
                    #TODO compute maximal size
                    self.max_size = 0

        print("Best orientation: {0}".format(self.best_orientation_vector))
        print("Best distance: {0}".format(self.best_dpt))
        print("Best area: {0}".format(self.max_area_safe))
        print("Best anchor: {0}".format(self.best_anchor))
        (best_bound1, best_bound2) = self.best_bounding
        print("Best bounds: {0}".format(self.best_bounding))

        if (abs(best_bound1[0] - best_bound2[0]) < EPS):
            # vertical line
            if (self.best_orientation_vector[0] > 0):
                rel = "<"
            else:
                rel = ">="
            new_constraints =  [Constraint(Poly(self.parameters[0] - best_bound1, self.parameters), rel, self.parameters)]
            print("line is described by x = {0}".format(best_bound1))
            print("constraint is x - {0} {1} 0".format(best_bound1, rel))
            return (new_constraints, self.max_size, self.max_area_safe)
        else:
            # asserted x2 != x1
            # slope m = (y2-y1) / (x2-x1)
            m = (best_bound2[1] - best_bound1[1]) / (best_bound2[0] - best_bound1[0])
            # two-point form
            #     y-y1 = m * (x-x1)
            # <=> 0 = mx - mx1 - y + y1
            # <=> 0 = mx - y + c with c = y1 - mx1
            c = best_bound1[1] - m * best_bound1[0]

            #TODO correct?
            if (self.best_orientation_vector[0] > 0):
                # part left of line is in constraint
                rel = ">"
            elif abs(self.best_orientation_vector[0]) < EPS and self.best_orientation_vector[1] > 0:
                # part below line is in constraint
                rel = ">"
            else:
                rel = "<="

            new_constraints = [Constraint(Poly(m*self.parameters[0] - self.parameters[1] + c, self.parameters), rel, self.parameters)]
            print("line is described by {m}x - y + {c} = 0".format(m=m, c=c))
            print("constraint is {m}x - y + {c} {r} 0".format(m=m, c=c, r=rel))
            return (new_constraints, self.max_size, self.max_area_safe)