import numpy as np
from numpy import linalg as LA

from numpy import cos, sin
import sampling

import sympy

import smt.smt
from config import *
import time
import tempfile

from data.constraint import *
from output.plot import *

#needed for pdf merging for debugging
from subprocess import call


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
    
def create_bounding_line(depth, rad, anchor):  
    
    if abs(rad - 1/2* np.pi) < 0.01:
        #TODO
        return ((0,depth), (1, depth))
    if abs(rad) < 0.01:
        #TODO
        return ((depth, 0), (depth, 1))
    if depth <= 1:
        if anchor[0] == anchor[1]:
            yintercept =  abs(anchor[1] - depth/cos(-rad))
            xintercept =  abs(anchor[0] - depth/cos(1/2 * np.pi + rad))
        else:
            xintercept =  abs(anchor[1] - depth/cos(-rad))
            yintercept =  abs(anchor[0] - depth/cos(1/2 * np.pi + rad))
        
        return ((anchor[0], yintercept), (xintercept,anchor[1]))
    else:
        #TODO
        return ((0, 0), (0,0))
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
            
            plot_results_bool(parameters, dict([(p, v > threshold) for p,v in samples.items()]), additional_lines = [create_bounding_line(dpt, -i/(2*steps)*np.pi, anchor)], additional_arrows = [(anchor, orientation_vector*dpt)], path_to_save = "tryout.png", display=True)
            
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
        e =  best_dpt/cos(1/2 * np.pi - best_rad)
        print(b)
        print(e)
        
        
        a =  -b / e
        print("constraint is {1}*x + {0}*y - {0}*{1} < 0".format(-a,b))
        print("line is described by {0}x + {1} = 0".format(a, b))
        return (best_safety, Constraint(sympy.Poly(b*parameters[0] - a*parameters[1] + a*b, parameters), rel, parameters))
    
def inside_rectangle(point, anchor_1, anchor_2, pos_x, pos_y):
    # checks if the point lies in the rectangle spanned by anchor_1
    if (pos_x and anchor_1[0] <= point[0] and point[0] <= anchor_2[0]) or (not pos_x and anchor_2[0] <= point[0] and point[0] <= anchor_1[0]):
        if (pos_y and anchor_1[1] <= point[1] and point[1] <= anchor_2[1]) or (not pos_y and anchor_2[1] <= point[1] and point[1] <= anchor_1[1]):
            return True
        else:
            return False
    else:
        return False
    
def point_fulfills_constraint(pt, parameters, constraint):
    pol = constraint.polynomial
    evaluation = zip(parameters, pt)
    
    for [variable, value] in evaluation:
        pol = pol.subs(variable, value).evalf(0.001)
    
    if constraint.relation == "=":
        return abs(pol) < 0.001
    elif constraint.relation == "<":
        return pol < 0
    elif constraint.relation == ">":
        return pol > 0
    elif constraint.relation == "<=":
        return pol <= 0
    elif constraint.relation == ">=":
        return pol >= 0
    elif constraint.relation == "<>":
        return abs(pol) > 0.001
    
    
def rectangle_constraints(p1, p2, parameters):
    pl = (min(p1[0], p2[0]), min(p1[1], p2[1]))
    ph = (max(p1[0], p2[0]), max(p1[1], p2[1]))
    
    
    constraints = [Constraint(Poly( parameters[0] - pl[0], parameters), ">=", parameters),
                   Constraint(Poly( parameters[1] - pl[1], parameters), ">=", parameters),
                   Constraint(Poly( parameters[0] - ph[0], parameters), "<=", parameters),
                   Constraint(Poly( parameters[1] - ph[1], parameters), "<=", parameters)]
    return constraints

def is_intersection(rectangle1, rectangle2):
    p11 = rectangle1[0]
    p12 = rectangle1[1]
    p21 = rectangle2[0]
    p22 = rectangle2[1]

    rec1_left = min(p11[0], p12[0])
    rec1_right = max(p11[0], p12[0])
    rec1_bottom = min(p11[1], p12[1])
    rec1_top = max(p11[1], p12[1])
    rec2_left = min(p21[0], p22[0])
    rec2_right = max(p21[0], p22[0])
    rec2_bottom = min(p21[1], p22[1])
    rec2_top = max(p21[1], p22[1])

    return rec1_left < rec2_right and rec2_left < rec1_right and rec1_bottom < rec2_top and rec2_bottom < rec1_top

def rectangle_subtract(fixed_point, point, rectangle2):
    # subtracts rectangle2 from rectangle spanned by fixed_point and point
    # fixed_point has to stay the same after subtraction
    # rectangle2 has to lie completely in rectangle_original
    # returns None if resulting rectangle is empty

    rec_original_left = min(fixed_point[0], point[0])
    rec_original_right = max(fixed_point[0], point[0])
    rec_original_bottom = min(fixed_point[1], point[1])
    rec_original_top = max(fixed_point[1], point[1])
    p21 = rectangle2[0]
    p22 = rectangle2[1]
    rec2_left = min(p21[0], p22[0])
    rec2_right = max(p21[0], p22[0])
    rec2_bottom = min(p21[1], p22[1])
    rec2_top = max(p21[1], p22[1])

    # compute intersection
    rec_intersect_left = max(rec_original_left, rec2_left);
    rec_intersect_bottom = max(rec_original_bottom, rec2_bottom);
    rec_intersect_right = min(rec_original_right, rec2_right);
    rec_intersect_top = min(rec_original_top, rec2_top);

    rec_remaining_left = rec_original_left
    rec_remaining_right = rec_original_right
    rec_remaining_bottom = rec_original_bottom
    rec_remaining_top = rec_original_top

    if (rec_original_left < rec_intersect_left):
        assert rec_original_right == rec_intersect_right
        rec_remaining_right = rec_intersect_left
    if (rec_original_right > rec_intersect_right):
        assert rec_original_left == rec_intersect_left
        rec_remaining_left = rec_intersect_right
    if (rec_original_bottom < rec_intersect_bottom):
        assert rec_original_top == rec_intersect_top
        rec_remaining_top = rec_intersect_bottom
    if (rec_original_top > rec_intersect_top):
        assert rec_original_bottom == rec_intersect_bottom
        rec_remaining_bottom = rec_intersect_top

    if (rec_original_left == rec_remaining_left and rec_original_right == rec_remaining_right and rec_original_bottom == rec_remaining_bottom and rec_original_top == rec_remaining_top):
        return None

    return ((rec_remaining_left, rec_remaining_bottom), (rec_remaining_right, rec_remaining_top))

def _print_benchmark_output(benchmark_output):
    i = 1
    print("no.  result   time  tot. time   area  tot. area")
    total_sec = 0
    total_area = 0
    for benchmark in benchmark_output:
        total_sec  =  total_sec + benchmark[1]
        if benchmark[0] == smt.smt.Answer.unsat:
            total_area =  total_area + benchmark[2]
        print("{:3}".format(i) + "   {:>5s}".format(benchmark[0].name) + "  {:5.2f}".format(benchmark[1]) + "     {:6.2f}".format(total_sec) + "  {:4.3f}".format(benchmark[2]) + "      {:4.3f}".format(total_area))
        i = i + 1
        
def growing_rectangle_constraints(samples_input, parameters, threshold, safe_above_threshold, smt2interface, ratfunc):  
    if len(parameters) != 2:
        raise NotImplementedError

    samples = samples_input.copy()
    
    
    anchor_points = [([(0,0)], True, True),
                     ([(1,0)], False, True), 
                     ([(1,1)], False, False),
                     ([(0,1)], True, False)]
    
    anchor_points_for_a_dir = anchor_points[0]
    succesfull_elimination = True
    safe_boxes = []
    unsafe_boxes = []
    benchmark_output = []
    plotdir = tempfile.mkdtemp(dir=PLOT_FILES_DIR)
    result_file = str(os.path.join(plotdir, "result.pdf"))
    result_tmp_file = str(os.path.join(plotdir, "result_tmp.pdf"))
    check_nr = 0
    while succesfull_elimination:
        check_nr = check_nr + 1
        succesfull_elimination = False
        max_size = 0
        max_pt = None
        best_anchor = None
        best_anchor_points_for_dir = None
        (safe_samples, bad_samples) = sampling.split_samples(samples, threshold, safe_above_threshold)
        assert(len(safe_samples) + len(bad_samples) == len(samples))
        for (anchor_points_for_a_dir, pos_x, pos_y)  in anchor_points:
            for anchor_point in anchor_points_for_a_dir:
                for point, value in samples.items():
                    # check if point lies in correct direction from anchor point
                    if not ((pos_x and point[0] > anchor_point[0]) or (not pos_x and point[0] < anchor_point[0])):
                        continue;
                    if not ((pos_y and point[1] > anchor_point[1]) or (not pos_y and point[1] < anchor_point[1])):
                        continue;
                    
                    break_attempt = False
                    # check for intersection with existing rectangles
                    for rectangle2 in safe_boxes + unsafe_boxes:
                        intersection = is_intersection((anchor_point, point), rectangle2)
                        if (intersection):
                            break_attempt = True
                            break
                            # TODO improve rectangle subtraction
                            ## reduce rectangle to part outside of existing rectangles
                            #rectangle_new = rectangle_subtract(anchor_point, point, rectangle2)
                            #if (rectangle_new != None):
                            #    plot_results_bool(parameters, dict([(p, v > threshold) for p,v in samples.items()]), anchor_points, additional_boxes_green = [(anchor_point, point)], additional_boxes_red = [rectangle2],  additional_boxes_blue = [rectangle_new], path_to_save = os.path.join(plotdir, "intersect.pdf"), display=True)
                            #    point = rectangle_new[0]
                            #    anchor_point = rectangle_new[1]

                    # choose largest rectangle
                    size = abs(point[0] - anchor_point[0]) * abs(point[1] - anchor_point[1])
                    if size > max_size and not break_attempt:
                        # check if nothing of other polarity is inbetween.
                        if (value > threshold and safe_above_threshold) or (value <= threshold and not safe_above_threshold):
                            safe_area = True
                            for point2, value2 in bad_samples.items():
                                if inside_rectangle(point2, anchor_point, point, pos_x, pos_y):
                                    # bad sample in safe area
                                    break_attempt = True
                                    break
                        else:
                            safe_area = False
                            for point2, value2 in safe_samples.items():
                                if inside_rectangle(point2, anchor_point, point, pos_x, pos_y):
                                    # safe sample in bad area
                                    break_attempt = True
                                    break
                        if not break_attempt:
                            # can extend area
                            max_size = size
                            max_area_safe = safe_area
                            max_pt = point
                            best_anchor = anchor_point
                            best_anchor_points_for_dir = anchor_points_for_a_dir
                            best_pos_x = pos_x
                            best_pos_y = pos_y
                            
        if max_pt != None and max_size > 0.0001:
            #print(smt2interface.version())
            #print("max_pt: {0}".format(max_pt))
            #print("best_anchor: {0}".format(best_anchor))
            #print("best_anchor_points_for_a_dir: {0}".format(best_anchor_points_for_dir))
            succesfull_elimination = True
            
            # plot result
            if max_area_safe:
                plot_results_bool(parameters, dict([(p, v > threshold) for p,v in samples.items()]), anchor_points, additional_boxes_green = [(best_anchor, max_pt)], path_to_save = os.path.join(plotdir, "call{0}.pdf".format(check_nr)), display=False)
            else:
                plot_results_bool(parameters, dict([(p, v > threshold) for p,v in samples.items()]), anchor_points, additional_boxes_red = [(best_anchor, max_pt)], path_to_save = os.path.join(plotdir, "call{0}.pdf".format(check_nr)), display=False)
            if check_nr == 1:
                call(["cp", str(os.path.join(plotdir, "call{0}.pdf".format(check_nr))), result_file])
            else:
                call(["pdfunite", result_file, str(os.path.join(plotdir, "call{0}.pdf".format(check_nr))), result_tmp_file])
                call(["mv", result_tmp_file, result_file])

            while True:
                smt2interface.push()
                curr_constraints = rectangle_constraints(best_anchor, max_pt, parameters)
                for constraint in curr_constraints:
                    smt2interface.assert_constraint(constraint)
                
                smt2interface.set_guard("safe", not max_area_safe)
                smt2interface.set_guard("bad", max_area_safe)
                print("Calling smt solver")
                start = time.time()
                checkresult = smt2interface.check()
                duration = time.time() - start
                print("Call took {0} seconds".format(duration))
                benchmark_output.append((checkresult, duration, abs(best_anchor[0] - max_pt[0])*abs(best_anchor[1] - max_pt[1])))
                if checkresult == smt.smt.Answer.killed or checkresult == smt.smt.Answer.memout:
                    smt2interface.pop()
                    if best_pos_x:
                        new_max_pt_x =  best_anchor[0] +  abs(best_anchor[0] - max_pt[0])/2
                    else:
                        new_max_pt_x =  best_anchor[0] -  abs(best_anchor[0] - max_pt[0])/2
                    if best_pos_y:
                        new_max_pt_y =  best_anchor[1] +  abs(best_anchor[1] - max_pt[1])/2
                    else:
                        new_max_pt_y =  best_anchor[1] -  abs(best_anchor[1] - max_pt[1])/2
                        
                    max_pt = (new_max_pt_x, new_max_pt_y)   
                    print("BBB max pt: {0}".format(max_pt))
                else: 
                    break

            if checkresult == smt.smt.Answer.unsat:
                print("AAA max pt: {0}".format(max_pt))

                # update anchor points for direction
                best_anchor_points_for_dir.append((max_pt[0], best_anchor[1]))
                best_anchor_points_for_dir.append((best_anchor[0], max_pt[1]))
                best_anchor_points_for_dir.remove(best_anchor)

                # remove unnecessary samples which are covered already by rectangle
                for pt, v in list(samples.items()):
                    fullfillsAllConstraints = True
                    for constraint in curr_constraints:
                        if not point_fulfills_constraint(pt, parameters, constraint):
                            fullfillsAllConstraints = False
                            break;
                    if fullfillsAllConstraints:
                        del samples[pt]

                # update anchor points
                print("anchor_points before: {0}".format(anchor_points))
                for (anchor_points_for_a_dir, pos_x, pos_y) in anchor_points:
                    if anchor_points_for_a_dir == best_anchor_points_for_dir:
                        continue
                    for anchor_point in anchor_points_for_a_dir:
                        if inside_rectangle(anchor_point, best_anchor, max_pt, best_pos_x, best_pos_y):
                            print(anchor_point)
                            print(max_pt)
                            anchor_points_for_a_dir.remove(anchor_point)
                            new_anchor = [0, 0]
                            if pos_x:
                                new_anchor[0] = max(anchor_point[0], max_pt[0]) 
                            else:
                                new_anchor[0] = min(anchor_point[0], max_pt[0])
                            if pos_y:
                                new_anchor[1] = max(anchor_point[1], max_pt[1]) 
                            else:
                                new_anchor[1] = min(anchor_point[1], max_pt[1]) 
                            anchor_points_for_a_dir.append(new_anchor)
                            print("updated {0} with {1}".format(anchor_point, new_anchor))

                #print("anchor_points after: {0}".format(anchor_points))

                if max_area_safe:
                    safe_boxes.append((best_anchor, max_pt))
                else: 
                    unsafe_boxes.append((best_anchor, max_pt))

                # plot result
                plot_results_bool(parameters, dict([(p, v > threshold) for p,v in samples.items()]), anchor_points, additional_boxes_green = safe_boxes, additional_boxes_red = unsafe_boxes, path_to_save = os.path.join(plotdir, "intermediate{0}.pdf".format(check_nr)), display=False)
                call(["pdfunite", result_file, str(os.path.join(plotdir, "intermediate{0}.pdf".format(check_nr))), result_tmp_file])
                call(["mv", result_tmp_file, result_file])

            elif checkresult == smt.smt.Answer.sat:
                model = smt2interface.get_model()
                modelPoint = tuple([model[p.name] for p in parameters])
                samples[modelPoint] = ratfunc.evaluate(list(model.items()))
                print("updated {0} with new value {1}".format(modelPoint, samples[modelPoint]))
            
            smt2interface.pop()
            _print_benchmark_output(benchmark_output)

    smt2interface.stop()
    smt2interface.print_calls()
    
    return
            
            