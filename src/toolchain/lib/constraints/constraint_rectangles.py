from constraint_generation import ConstraintGeneration
from data.constraint import Constraint
from sympy.polys.polytools import Poly

# TODO own rectangle class?
class ConstraintRectangles(ConstraintGeneration):

    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc):
        ConstraintGeneration.__init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc)

        self.anchor_points = [([(0, 0)], True, True),
                         ([(1, 0)], False, True),
                         ([(1, 1)], False, False),
                         ([(0, 1)], True, False)]

        self.safe_boxes = []
        self.unsafe_boxes = []

        self.max_size = 0
        self.max_pt = None
        self.max_area_safe = None
        self.best_anchor = None
        self.best_anchor_points_for_dir = None
        self.best_pos_x = None
        self.best_pos_y = None

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


        constraints = [Constraint(Poly(parameters[0] - pl[0], parameters), ">=", parameters),
                       Constraint(Poly(parameters[1] - pl[1], parameters), ">=", parameters),
                       Constraint(Poly(parameters[0] - ph[0], parameters), "<=", parameters),
                       Constraint(Poly(parameters[1] - ph[1], parameters), "<=", parameters)]
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

    def change_current_constraint(self):
        # change current constraint to avoid memout in smt
        # returns (new_constraint, new_covered_area)
        if self.best_pos_x:
            new_max_pt_x = self.best_anchor[0] + abs(self.best_anchor[0] - self.max_pt[0]) / 2
        else:
            new_max_pt_x = self.best_anchor[0] - abs(self.best_anchor[0] - self.max_pt[0]) / 2

        if self.best_pos_y:
            new_max_pt_y = self.best_anchor[1] + abs(self.best_anchor[1] - self.max_pt[1]) / 2
        else:
            new_max_pt_y = self.best_anchor[1] - abs(self.best_anchor[1] - self.max_pt[1]) / 2

        self.max_pt = (new_max_pt_x, new_max_pt_y)
        self.max_size = abs(self.best_anchor[0] - self.max_pt[0]) * abs(self.best_anchor[1] - self.max_pt[1])
        new_constraints = self.create_rectangle_constraints(self.best_anchor, self.max_pt, self.parameters)
        return (new_constraints, self.max_size, self.max_area_safe)

    def finalize_step(self):
        # update anchor points for direction
        self.best_anchor_points_for_dir.append((self.max_pt[0], self.best_anchor[1]))
        self.best_anchor_points_for_dir.append((self.best_anchor[0], self.max_pt[1]))
        self.best_anchor_points_for_dir.remove(self.best_anchor)

        # update anchor points
        print("anchor_points before: {0}".format(self.anchor_points))
        for (anchor_points_for_a_dir, pos_x, pos_y) in self.anchor_points:
            if anchor_points_for_a_dir == self.best_anchor_points_for_dir:
                continue
            for anchor_point in anchor_points_for_a_dir:
                if self.is_inside_rectangle(anchor_point, self.best_anchor, self.max_pt, self.best_pos_x, self.best_pos_y):
                    print(anchor_point)
                    print(self.max_pt)
                    anchor_points_for_a_dir.remove(anchor_point)
                    new_anchor = [0, 0]
                    if pos_x:
                        new_anchor[0] = max(anchor_point[0], self.max_pt[0])
                    else:
                        new_anchor[0] = min(anchor_point[0], self.max_pt[0])
                    if pos_y:
                        new_anchor[1] = max(anchor_point[1], self.max_pt[1])
                    else:
                        new_anchor[1] = min(anchor_point[1], self.max_pt[1])
                    anchor_points_for_a_dir.append(new_anchor)
                    print("updated {0} with {1}".format(anchor_point, new_anchor))

        print("anchor_points after: {0}".format(self.anchor_points))

        if self.max_area_safe:
            self.safe_boxes.append((self.best_anchor, self.max_pt))
        else:
            self.unsafe_boxes.append((self.best_anchor, self.max_pt))

        self.plot_results(self.anchor_points, additional_boxes_green = self.safe_boxes, additional_boxes_red = self.unsafe_boxes, name = "intermediate{0}".format(self.nr), display = False)

    def next_constraint(self):
        # computes next rectangle constraint
        # returns (new_constraint, new_covered_area)

        # reset
        self.max_size = 0
        self.max_pt = None
        self.max_area_safe = None
        self.best_anchor = None
        self.best_anchor_points_for_dir = None
        self.best_pos_x = None
        self.best_pos_y = None

        for (anchor_points_for_a_dir, pos_x, pos_y) in self.anchor_points:
            for anchor_point in anchor_points_for_a_dir:
                for point, value in self.samples.items():
                    # check if point lies in correct direction from anchor point
                    if not ((pos_x and point[0] > anchor_point[0]) or (not pos_x and point[0] < anchor_point[0])):
                        continue;
                    if not ((pos_y and point[1] > anchor_point[1]) or (not pos_y and point[1] < anchor_point[1])):
                        continue;

                    break_attempt = False
                    # check for intersection with existing rectangles
                    # TODO make more efficient
                    for rectangle2 in self.safe_boxes + self.unsafe_boxes:
                        intersection = self.is_intersection((anchor_point, point), rectangle2)
                        if (intersection):
                            break_attempt = True
                            break
                            # TODO improve rectangle subtraction
                            # # reduce rectangle to part outside of existing rectangles
                            # rectangle_new = self.rectangle_subtract(anchor_point, point, rectangle2)
                            # if (rectangle_new != None):
                            #    Plot.plot_results(parameters, dict([(p, v > threshold) for p,v in samples.items()]), anchor_points, additional_boxes_green = [(anchor_point, point)], additional_boxes_red = [rectangle2],  additional_boxes_blue = [rectangle_new], path_to_save = os.path.join(self.plotdir, "intersect.pdf"), display=True)
                            #    point = rectangle_new[0]
                            #    anchor_point = rectangle_new[1]

                    # choose largest rectangle
                    size = abs(point[0] - anchor_point[0]) * abs(point[1] - anchor_point[1])
                    if size > self.max_size and not break_attempt:
                        # check if nothing of other polarity is inbetween.
                        if (value > self.threshold and self.safe_above_threshold) or (value <= self.threshold and not self.safe_above_threshold):
                            safe_area = True
                            for point2, value2 in self.bad_samples.items():
                                if self.is_inside_rectangle(point2, anchor_point, point, pos_x, pos_y):
                                    # bad sample in safe area
                                    break_attempt = True
                                    break
                        else:
                            safe_area = False
                            for point2, value2 in self.safe_samples.items():
                                if self.is_inside_rectangle(point2, anchor_point, point, pos_x, pos_y):
                                    # safe sample in bad area
                                    break_attempt = True
                                    break

                        if not break_attempt:
                            # can extend area
                            self.max_size = size
                            self.max_area_safe = safe_area
                            self.max_pt = point
                            self.best_anchor = anchor_point
                            self.best_anchor_points_for_dir = anchor_points_for_a_dir
                            self.best_pos_x = pos_x
                            self.best_pos_y = pos_y

        if self.max_pt is not None and self.max_size > self.threshold_area:
            # plot result
            if self.max_area_safe:
                self.plot_results(self.anchor_points, additional_boxes_green = [(self.best_anchor, self.max_pt)], name = "call{0}".format(self.nr), display = False, first = (self.nr == 1))
            else:
                self.plot_results(self.anchor_points, additional_boxes_red = [(self.best_anchor, self.max_pt)], name = "call{0}".format(self.nr), display = False, first = (self.nr == 1))
            new_constraints = self.create_rectangle_constraints(self.best_anchor, self.max_pt, self.parameters)
            return (new_constraints, self.max_size, self.max_area_safe)
        else:
            return None
