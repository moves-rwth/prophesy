from constraint_generation import *

import numpy as np
from numpy import cos, sin
import sympy

class ConstraintPlanes(ConstraintGeneration):
    
    def __init__(self, _steps=3):
        ConstraintGeneration.__init__(self)
        self.steps = _steps
        self.deg90 = 1/2 * np.pi;

    def create_halfspace_depth(self, safe_samples, bad_samples, anchor_point, orientation_vector):
        assert(np.linalg.norm(orientation_vector) == 1)

        # compute minimal/maximal safe/bad distances
        min_safe_dist = 1000
        min_bad_dist = 1000
        max_safe_dist = 0
        max_bad_dist = 0

        for k,v in safe_samples.items():
            weighted_dist = np.dot(k - anchor_point, orientation_vector)
            if weighted_dist < min_safe_dist:
                min_safe_dist = weighted_dist
            if weighted_dist > max_safe_dist:
                max_safe_dist = weighted_dist
        for k,v in bad_samples.items():
            weighted_dist = np.dot(k - anchor_point, orientation_vector)
            if weighted_dist < min_bad_dist:
                min_bad_dist = weighted_dist
            if weighted_dist > max_bad_dist:
                max_bad_dist = weighted_dist

        if min_safe_dist == min_bad_dist:
            return (True, 0)
        elif min_safe_dist < min_bad_dist:
            safe = True
        else: 
            assert(min_safe_dist > min_bad_dist)
            safe = False

        print("\t\tmin_safe_dist: {0}".format(min_safe_dist))
        print("\t\tmin_bad_dist: {0}".format(min_bad_dist))

        if safe:
            depth_pt = min_bad_dist
            #depth_pt = min(min_bad_dist - min_bad_dist/10, min_bad_dist + max_safe_dist / 2)
        else:
            depth_pt = min_safe_dist
            #depth_pt = min(min_safe_dist - min_safe_dist/10, min_safe_dist + max_bad_dist / 2)
        return (safe, depth_pt)

    def create_bounding_line(self, depth, rad, anchor):
        bound1 = (0, 0)
        bound2 = (0, 0)
        if abs(rad - self.deg90) < EPS:
            #TODO
            # horizontal
            bound1 = (0, depth)
            bound2 = (1, depth)
        elif abs(rad) < EPS:
            #TODO
            # vertical
            bound1 = (depth, 0)
            bound2 = (depth, 1)
        elif depth <= 1:
            if anchor[0] == anchor[1]:
                yintercept =  abs(anchor[1] - depth/cos(-rad))
                xintercept =  abs(anchor[0] - depth/cos(self.deg90 + rad))
            else:
                #TODO correct to switch x and y?
                xintercept =  abs(anchor[1] - depth/cos(-rad))
                yintercept =  abs(anchor[0] - depth/cos(self.deg90 + rad))

            bound1 = (anchor[0], yintercept)
            bound2 = (xintercept,anchor[1])
        else:
            #TODO
            # no valid depth
            assert(False)

        # check orthogonality
        orientation_vector = self.rotate_vector((1,0), rad)
        bound_direction = (bound1[0] - bound2[0], bound1[1] - bound2[1])
        print(orientation_vector)
        print(bound1)
        print(bound2)
        print(bound_direction)
        assert(abs(np.dot(orientation_vector, bound_direction)) < EPS)
        return (bound1, bound2)

    def rotate_vector(self, x, rad):
        R = np.matrix([[np.cos(rad), -np.sin(rad)],[np.sin(rad), np.cos(rad)]])
        return x * R

    def normalize_vector(self, x):
        return x / np.linalg.norm(x)

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
                print("\to-vec: {0}".format(orientation_vector))
                (safety, dpt) =  self.create_halfspace_depth(safe_samples, bad_samples, anchor, orientation_vector)
                nr += 1
                Plot.plot_results(parameters, dict([(p, v > threshold) for p,v in samples.items()]), additional_lines = [self.create_bounding_line(dpt, i*step_radius, anchor)], additional_arrows = [(anchor, orientation_vector*dpt)], path_to_save = os.path.join(self.plotdir, "call{0}.pdf".format(nr)), display=True)
                self.add_pdf("call{0}".format(nr), nr == 1)

                if dpt > best_dpt:
                    best_orientation_vector = orientation_vector
                    best_dpt = dpt
                    best_safety = safety
                    best_rad = step_radius
                    best_anchor = anchor

                orientation_vector = self.normalize_vector(self.rotate_vector(orientation_vector, step_radius))
                # necessary? iteration necessary?
                if abs(orientation_vector.item(0)) < EPS:
                    n0 = 0
                else:
                    n0 = orientation_vector.item(0)
                if abs(orientation_vector.item(1)) < EPS:
                    n1 = 0
                else:
                    n1 = orientation_vector.item(1)
                orientation_vector = self.normalize_vector(np.array([n0, n1]))

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