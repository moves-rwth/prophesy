from constraint_generation import *

class ConstraintRectangles(ConstraintGeneration):
    
    
    
    def __init__(self, _smt2interface, _ratfunc):
        self.smt2interface = _smt2interface
        self.ratfunc = _ratfunc
        print("test")

    def is_inside_rectangle(self, point, anchor_1, anchor_2, pos_x, pos_y):
        # checks if the point lies in the rectangle spanned by anchor_1
        if (pos_x and anchor_1[0] <= point[0] and point[0] <= anchor_2[0]) or (not pos_x and anchor_2[0] <= point[0] and point[0] <= anchor_1[0]):
            if (pos_y and anchor_1[1] <= point[1] and point[1] <= anchor_2[1]) or (not pos_y and anchor_2[1] <= point[1] and point[1] <= anchor_1[1]):
                return True
            else:
                return False
        else:
            return False

    def create_rectangle_constraints(self, p1, p2, parameters):
        pl = (min(p1[0], p2[0]), min(p1[1], p2[1]))
        ph = (max(p1[0], p2[0]), max(p1[1], p2[1]))


        constraints = [Constraint(Poly( parameters[0] - pl[0], parameters), ">=", parameters),
                       Constraint(Poly( parameters[1] - pl[1], parameters), ">=", parameters),
                       Constraint(Poly( parameters[0] - ph[0], parameters), "<=", parameters),
                       Constraint(Poly( parameters[1] - ph[1], parameters), "<=", parameters)]
        return constraints

    def is_intersection(self, rectangle1, rectangle2):
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

    def rectangle_subtract(self, fixed_point, point, rectangle2):
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

    def generate_constraints(self, samples_input, parameters, threshold, safe_above_threshold, threshold_area):
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
                        # TODO make more efficient
                        for rectangle2 in safe_boxes + unsafe_boxes:
                            intersection = self.is_intersection((anchor_point, point), rectangle2)
                            if (intersection):
                                break_attempt = True
                                break
                                # TODO improve rectangle subtraction
                                ## reduce rectangle to part outside of existing rectangles
                                #rectangle_new = self.rectangle_subtract(anchor_point, point, rectangle2)
                                #if (rectangle_new != None):
                                #    Plot.plot_results(parameters, dict([(p, v > threshold) for p,v in samples.items()]), anchor_points, additional_boxes_green = [(anchor_point, point)], additional_boxes_red = [rectangle2],  additional_boxes_blue = [rectangle_new], path_to_save = os.path.join(plotdir, "intersect.pdf"), display=True)
                                #    point = rectangle_new[0]
                                #    anchor_point = rectangle_new[1]

                        # choose largest rectangle
                        size = abs(point[0] - anchor_point[0]) * abs(point[1] - anchor_point[1])
                        if size > max_size and not break_attempt:
                            # check if nothing of other polarity is inbetween.
                            if (value > threshold and safe_above_threshold) or (value <= threshold and not safe_above_threshold):
                                safe_area = True
                                for point2, value2 in bad_samples.items():
                                    if self.is_inside_rectangle(point2, anchor_point, point, pos_x, pos_y):
                                        # bad sample in safe area
                                        break_attempt = True
                                        break
                            else:
                                safe_area = False
                                for point2, value2 in safe_samples.items():
                                    if self.is_inside_rectangle(point2, anchor_point, point, pos_x, pos_y):
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

            if max_pt != None and max_size > threshold_area:
                #print(smt2interface.version())
                #print("max_pt: {0}".format(max_pt))
                #print("best_anchor: {0}".format(best_anchor))
                #print("best_anchor_points_for_a_dir: {0}".format(best_anchor_points_for_dir))
                succesfull_elimination = True

                # plot result
                if max_area_safe:
                    Plot.plot_results(parameters, dict([(p, v > threshold) for p,v in samples.items()]), anchor_points, additional_boxes_green = [(best_anchor, max_pt)], path_to_save = os.path.join(plotdir, "call{0}.pdf".format(check_nr)), display=False)
                else:
                    Plot.plot_results(parameters, dict([(p, v > threshold) for p,v in samples.items()]), anchor_points, additional_boxes_red = [(best_anchor, max_pt)], path_to_save = os.path.join(plotdir, "call{0}.pdf".format(check_nr)), display=False)
                if check_nr == 1:
                    call(["cp", str(os.path.join(plotdir, "call{0}.pdf".format(check_nr))), result_file])
                else:
                    call(["pdfunite", result_file, str(os.path.join(plotdir, "call{0}.pdf".format(check_nr))), result_tmp_file])
                    call(["mv", result_tmp_file, result_file])

                while True:
                    self.smt2interface.push()
                    curr_constraints = self.create_rectangle_constraints(best_anchor, max_pt, parameters)
                    for constraint in curr_constraints:
                        self.smt2interface.assert_constraint(constraint)

                    self.smt2interface.set_guard("safe", not max_area_safe)
                    self.smt2interface.set_guard("bad", max_area_safe)
                    print("Calling smt solver")
                    start = time.time()
                    checkresult = self.smt2interface.check()
                    duration = time.time() - start
                    print("Call took {0} seconds".format(duration))
                    benchmark_output.append((checkresult, duration, abs(best_anchor[0] - max_pt[0])*abs(best_anchor[1] - max_pt[1])))
                    if checkresult == smt.smt.Answer.killed or checkresult == smt.smt.Answer.memout:
                        self.smt2interface.pop()
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
                            if not self.is_point_fulfilling_constraint(pt, parameters, constraint):
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
                            if self.is_inside_rectangle(anchor_point, best_anchor, max_pt, best_pos_x, best_pos_y):
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
                    Plot.plot_results(parameters, dict([(p, v > threshold) for p,v in samples.items()]), anchor_points, additional_boxes_green = safe_boxes, additional_boxes_red = unsafe_boxes, path_to_save = os.path.join(plotdir, "intermediate{0}.pdf".format(check_nr)), display=False)
                    call(["pdfunite", result_file, str(os.path.join(plotdir, "intermediate{0}.pdf".format(check_nr))), result_tmp_file])
                    call(["mv", result_tmp_file, result_file])

                elif checkresult == smt.smt.Answer.sat:
                    model = self.smt2interface.get_model()
                    modelPoint = tuple([model[p.name] for p in parameters])
                    samples[modelPoint] = self.ratfunc.evaluate(list(model.items()))
                    print("updated {0} with new value {1}".format(modelPoint, samples[modelPoint]))

                self.smt2interface.pop()
                self.print_benchmark_output(benchmark_output)

        self.smt2interface.stop()
        self.smt2interface.print_calls()

        return

            