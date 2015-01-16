from constraint_generation import *

import numpy as np
from numpy import cos, sin
import sympy

class ConstraintPlanes(ConstraintGeneration):
    
    def __init__(self, _steps=3):
        ConstraintGeneration.__init__(self)
        self.steps = _steps
        self.deg90 = 1/2 * np.pi;

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
        print(orthogonal_vec)

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

        print("orientation: {0}".format(orientation_vector))
        orthogonal_anchor = anchor + orientation_vector
        orthogonal_vec = self.compute_orthogonal_vector(orientation_vector)
        print("orthogonal anchor: {0}".format(orthogonal_anchor))
        print("orthogonal vector: {0}".format(orthogonal_vec))

        # intersection with borders
        down = self.get_intersection(orthogonal_anchor, orthogonal_vec, np.array([0,0]), np.array([1,0]))
        left = self.get_intersection(orthogonal_anchor, orthogonal_vec, np.array([0,0]), np.array([0,1]))
        top = self.get_intersection(orthogonal_anchor, orthogonal_vec, np.array([0,1]), np.array([1,0]))
        right = self.get_intersection(orthogonal_anchor, orthogonal_vec, np.array([1,0]), np.array([0,1]))
        print("Borders: {0}, {1}, {2}, {3}".format(down, left, top, right))
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

    def generate_constraints(self, samples, parameters, threshold, safe_above_threshold, threshold_area):
        if len(parameters) != 2:
            raise NotImplementedError
        (safe_samples, bad_samples) = sampling.split_samples(samples, threshold, safe_above_threshold)

        anchor_points = [np.array([0,0]), np.array([1,0]), np.array([1,1]), np.array([0,1])]

        best_orientation_vector = np.array([0,0])
        best_dpt = 0
        best_safety = False

        orientation_vector = np.array([1,0])
        nr = 0
        step_radius = -self.deg90/self.steps
        for anchor in anchor_points:
            print("anchor: {0}".format(anchor))
            for i in range(0, self.steps):
                nr += 1
                # orientation vector according to 90°/steps
                orientation_vector = self.normalize_vector(self.rotate_vector(np.array([1,0]), i*step_radius))
                print("\to-vec: {0}".format(orientation_vector))

                (safety, dpt) =  self.create_halfspace_depth(safe_samples, bad_samples, anchor, orientation_vector)
                if abs(dpt) < EPS:
                    continue
                result_bounding = self.create_bounding_line(anchor, orientation_vector*dpt)
                if result_bounding is None:
                    continue
                (bound1, bound2) = result_bounding
                print("bounding line: {0}, {1}".format(bound1, bound2))
                Plot.plot_results(parameters, dict([(p, v > threshold) for p,v in samples.items()]), additional_lines = [(bound1, bound2)], additional_arrows = [(anchor, orientation_vector*dpt), (anchor, orientation_vector)], path_to_save = os.path.join(self.plotdir, "call{0}.pdf".format(nr)), display=True)
                self.add_pdf("call{0}".format(nr), nr == 1)

                # chooose best
                if dpt > best_dpt:
                    best_orientation_vector = orientation_vector
                    best_dpt = dpt
                    best_safety = safety
                    best_rad = step_radius
                    best_anchor = anchor

        print(best_orientation_vector)
        print(best_dpt)
        print(best_safety)
        print(best_anchor)

        if best_anchor[0] == 0:
            rel = "<"
        else:
            rel = ">="

        if best_orientation_vector.item(0) == 0:
            return (best_safety, Constraint(sympy.Poly(parameters[1] - best_dpt, parameters), rel, parameters))
        elif best_orientation_vector.item(1) == 0:
            return (best_safety, Constraint(sympy.Poly(parameters[0] - best_dpt, parameters), rel, parameters))
        else:    
            b =  best_dpt/cos(best_rad)
            e =  best_dpt/cos(self.deg90 - best_rad)
            print(b)
            print(e)

            a =  -b / e
            print("constraint is {1}*x - {0}*y + {0}*{1} {2} 0".format(a,b,rel))
            print("line is described by {0}x + {1} = 0".format(a, b))
            return (best_safety, Constraint(sympy.Poly(b*parameters[0] - a*parameters[1] + a*b, parameters), rel, parameters))