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
    
def create_halfspace_constraint(samples, parameters, threshold, safe_above_threshold, steps=2):
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
    

    
