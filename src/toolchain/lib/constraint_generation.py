import numpy as np
from numpy import linalg as LA

from numpy import cos, sin
import sampling

import sympy

from data.constraint import *
from output.plot import *

def _halfspace_constraint(safe_samples, bad_samples, orientation_vector, anchor_point):
    assert(np.linalg.norm(orientation_vector) == 1)
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
        dpt = min_bad_dist
        #dpt = min(min_bad_dist - min_bad_dist/10, min_bad_dist + max_safe_dist / 2)
    else:
        dpt = min_safe_dist
        #dpt = min(min_safe_dist - min_safe_dist/10, min_safe_dist + max_bad_dist / 2)
    return (safe, dpt)    
    
    
def rotate_vector(x, rad):
    R = np.matrix([[np.cos(rad), -np.sin(rad)],[np.sin(rad), np.cos(rad)]])
    return x * R
    
def normalize_vector(x):
    return x / np.linalg.norm(x)
    
def create_halfspace_constraint(samples, parameters, threshold, safe_above_threshold, steps=3):
    if len(parameters) != 2:
        raise NotImplementedError
    (safe_samples, bad_samples) = sampling.split_samples(samples, threshold, safe_above_threshold)
    
    anchor_points = [np.array([0,0]),np.array([1,0]), np.array([1,1]), np.array([0,1])]
    
    best_orientation_vector = np.array([0,0])
    best_dpt = 0
    best_safety = False
    
    orientation_vector = np.array([1,0])
    for anchor in anchor_points:
        print("anchor: {0}".format(anchor))
        for i in range(0, steps):
            print("\to-vec: {0}".format(orientation_vector))
            (safety, dpt) =  _halfspace_constraint(safe_samples, bad_samples, orientation_vector, anchor)  
            plot_results_bool(parameters, dict([(p, v > threshold) for p,v in samples.items()]), [(anchor, orientation_vector*dpt)])
            if dpt > best_dpt:
                best_orientation_vector = orientation_vector
                best_dpt = dpt
                best_safety = safety
                best_rad = -1/(2*steps)*np.pi
                best_anchor = anchor
                
            orientation_vector = normalize_vector(rotate_vector(orientation_vector, -1/(2*steps)*np.pi))
            if abs(orientation_vector.item(0)) < 0.001:
                n0 = 0
            else:
                n0 = orientation_vector.item(0)
            if abs(orientation_vector.item(1)) < 0.001:
                n1 = 0
            else:
                n1 = orientation_vector.item(1)
            orientation_vector = normalize_vector(np.array([n0, n1]))
            
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
        e =  best_dpt/cos(1/4 * np.pi - best_rad)
        print(b)
        print(e)
        
        
        a =  -b / e
        print("constraint is {1}*x + {0}*y - {0}*{1} < 0".format(-a,b))
        print("line is described by {0}x + {1} = 0".format(a, b))
        return (best_safety, Constraint(sympy.Poly(b*parameters[0] - a*parameters[1] + a*b, parameters), rel, parameters))
    
def inside_rectangle(point, anchor_1, anchor_2, pos_x, pos_y):
    if (pos_x and anchor_1[0] <= point[0] and point[0] <= anchor_2[0]) or (not pos_x and anchor_2[0] <= point[0] and point[0] <= anchor_1[0]):
        if (pos_y and anchor_1[1] <= point[1] and point[1] <= anchor_2[1]) or (not pos_y and anchor_2[1] <= point[1] and point[1] <= anchor_1[1]):
            return True
        else:
            return False
    else:
        return False
    
def growing_rectangle_constraints(samples, parameters, threshold, safe_above_threshold):  
    if len(parameters) != 2:
        raise NotImplementedError
    (safe_samples, bad_samples) = sampling.split_samples(samples, threshold, safe_above_threshold)
    assert(len(safe_samples) + len(bad_samples) == len(samples))
    print(bad_samples)
    print(safe_samples)
    
    print(safe_above_threshold)
    anchor_points = [([np.array([0,0])], True, True),
                     ([np.array([1,0])], False, True), 
                     ([np.array([1,1])], False, False),
                     ([np.array([0,1])], True, False)]
    
    anchor_points_for_a_dir = anchor_points[0]
    succesfull_elimination = True
    while succesfull_elimination:
        succesfull_elimination = False
        max_size = 0
        max_pt = None
        best_anchor = None
        best_anchor_points_for_dir = None
        for (anchor_points_for_a_dir, pos_x, pos_y)  in anchor_points:
            for anchor_point in anchor_points_for_a_dir:
                for pt, v in samples.items():
                    print("pt = {0}".format(pt))
                    print(v)
                    if not ((pos_x and pt[0] > anchor_point[0]) or (not pos_x and pt[0] < anchor_point[0])):
                        continue;
                    if not ((pos_y and pt[1] > anchor_point[1]) or (not pos_y and pt[1] < anchor_point[1])):
                        continue;
                    
                    size = abs(pt[0] - anchor_point[0]) * abs(pt[1] - anchor_point[1])
                    if size > max_size:
                        break_attempt = False
                        # check if nothing of other polarity is inbetween.
                        if (v > threshold and safe_above_threshold) or (v <= threshold and not safe_above_threshold):
                            for pt2, v2 in bad_samples.items():
                                print("\tpt2 = {0}".format(pt2))
                                if inside_rectangle(pt2, anchor_point, pt, pos_x, pos_y):
                                    break_attempt = True
                                    break
                        else:
                            for pt2, v2 in safe_samples.items():
                                print("\tpt2 = {0}".format(pt2))
                                if inside_rectangle(pt2, anchor_point, pt, pos_x, pos_y):
                                    break_attempt = True
                                    break 
                        if not break_attempt:
                            max_size = size
                            max_pt = pt
                            best_anchor = anchor_point
                            best_anchor_points_for_dir = anchor_points_for_a_dir
                            
        if max_pt != None:
            print(max_pt)
            print("best_anchor: {0}".format(best_anchor))
            plot_results_bool(parameters, dict([(p, v > threshold) for p,v in samples.items()]), [], [(best_anchor, max_pt)])
            succesfull_elimination = True
            best_anchor_points_for_dir.remove(best_anchor)
            best_anchor_points_for_dir.append(np.array([max_pt[0], best_anchor[1]]))
            best_anchor_points_for_dir.append(np.array([best_anchor[0], max_pt[1]]))
            
            