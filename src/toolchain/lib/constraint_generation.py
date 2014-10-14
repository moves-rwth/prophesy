import numpy as np
from numpy import linalg as LA

from numpy import cos, sin
import sampling

def _halfspace_constraint(safe_samples, bad_samples, orientation_vector):
    assert(np.linalg.norm(orientation_vector) == 1)
    min_safe_dist = 1000
    min_bad_dist = 1000
    max_safe_dist = 0
    max_bad_dist = 0
    
    for k,v in safe_samples.items():
        weighted_dist = np.dot(k, orientation_vector)
        if weighted_dist < min_safe_dist:
            min_safe_dist = weighted_dist
        if weighted_dist > max_safe_dist:
            max_safe_dist = weighted_dist
    for k,v in bad_samples.items():
        weighted_dist = np.dot(k, orientation_vector)
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
    
    
    if safe:
        dpt = min_bad_dist
        #dpt = min(min_bad_dist - min_bad_dist/10, min_bad_dist + max_safe_dist / 2)
    else:
        dpt = min_safe_dist
        #dpt = min(min_safe_dist - min_safe_dist/10, min_safe_dist + max_bad_dist / 2)
    return (safe, dpt)    
    
    #print(max_safe_dist)
    #print(max_bad_dist)
    
def rotate_vector(x, rad):
    R = np.matrix([[np.cos(rad), -np.sin(rad)],[np.sin(rad), np.cos(rad)]])
    return x * R
    
def normalize_vector(x):
    return x / np.linalg.norm(x)
    
def create_halfspace_constraint(samples, threshold, safe_above_threshold, steps=4):
    (safe_samples, bad_samples) = sampling.split_samples(samples, threshold, safe_above_threshold)
    best_orientation_vector = np.array([0,0])
    best_dpt = 0
    best_safety = False
    orientation_vector = np.array([1,0])
    for i in range(0, steps):
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
        (safety, dpt) =  _halfspace_constraint(safe_samples, bad_samples, orientation_vector)    
        if dpt > best_dpt:
            best_orientation_vector = orientation_vector
            best_dpt = dpt
            best_safety = safety
            best_rad = -1/(2*steps)*np.pi
    print(best_orientation_vector)
    print(best_dpt)
    print(best_safety)
    
    b =  best_dpt/cos(best_rad)
    e =  best_dpt/cos(1/4 * np.pi - best_rad)
    print(b)
    print(e)
    
    
    a =  -b / e
    print("constraint is x/{0} + y/{1} < 1".format(-a,b))
    print("line is described by {0}x + {1} = 0".format(a, b))
    
    

    
