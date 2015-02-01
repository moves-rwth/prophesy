from constraint_generation import ConstraintGeneration, Anchor, Direction
from data.constraint import Constraint
from sympy.polys.polytools import Poly
from shapely.geometry import box, Point
from shapely import affinity
import sampling

class ConstraintRectangles(ConstraintGeneration):

    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc):
        ConstraintGeneration.__init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc)

        self.anchor_points = [Anchor(Point(0, 0), Direction.NE),
                         Anchor(Point(1, 0), Direction.NW),
                         Anchor(Point(1, 1), Direction.SW),
                         Anchor(Point(0, 1), Direction.SE)]

        self.safe_boxes = []
        self.unsafe_boxes = []

        self.max_area_safe = None
        self.best_anchor = None
        self.best_anchor_points_for_dir = None
        self.best_rectangle = None
        self.best_other_point = None
        self.max_size = 0
        self.best_pos_x = None
        self.best_pos_y = None

    def is_inside_rectangle(self, point, rectangle):
        # checks if the point lies in the rectangle
        return point.within(rectangle) or point.touches(rectangle)

    def intersects(self, rectangle1, rectangle2):
        # checks if rectangles intersect, touching is okay
        return rectangle1.intersects(rectangle2) and not rectangle1.touches(rectangle2)

    def create_rectangle_constraints(self, rectangle, parameters):
        (x1, y1, x2, y2) = rectangle.bounds
        assert(x1 <= x2)
        assert(y1 <= y2)

        p = Poly(parameters[0] - x1, parameters)
        constraints = [Constraint(Poly(parameters[0] - x1, parameters), ">=", parameters),
                       Constraint(Poly(parameters[1] - y1, parameters), ">=", parameters),
                       Constraint(Poly(parameters[0] - x2, parameters), "<=", parameters),
                       Constraint(Poly(parameters[1] - y2, parameters), "<=", parameters)]
        return constraints

    def change_current_constraint(self):
        # change current constraint to avoid memout in smt
        # returns (new_constraint, new_covered_area, area_safe)

        # scale rectangle by factor 0.5
        self.best_rectangle = affinity.scale(self.best_rectangle, xfact=0.5, yfact=0.5, origin=self.best_anchor)
        (x1, y1, x2, y2) = self.best_rectangle.bounds
        self.best_other_point = (x2 if self.best_pos_x else x1, y2 if self.best_pos_y else y1)
        return (self.create_constraint(self.best_rectangle), self.best_rectangle, self.max_area_safe)

    def finalize_step(self, new_constraint):
        # update anchor points for direction
        self.best_anchor_points_for_dir.append(Point(self.best_other_point.x, self.best_anchor.y))
        self.best_anchor_points_for_dir.append(Point(self.best_anchor.x, self.best_other_point.y))
        self.best_anchor_points_for_dir.remove(self.best_anchor)

        # update anchor points
        #print("anchor_points before: {0}".format(self.anchor_points))
        (x1, y1, x2, y2) = self.best_rectangle.bounds
        for (anchor_points_for_a_dir, pos_x, pos_y) in self.anchor_points:
            if anchor_points_for_a_dir == self.best_anchor_points_for_dir:
                continue
            new_x = x2 if pos_x else x1
            new_y = y2 if pos_y else y1
            for anchor_point in anchor_points_for_a_dir:
                if self.is_inside_rectangle(anchor_point, self.best_rectangle):
                    print(anchor_point)
                    anchor_points_for_a_dir.remove(anchor_point)
                    new_anchor = Point(new_x, new_y)
                    anchor_points_for_a_dir.append(new_anchor)
                    print("updated {0} with {1}".format(anchor_point, new_anchor))

        #print("anchor_points after: {0}".format(self.anchor_points))

        if self.max_area_safe:
            self.safe_boxes.append(self.best_rectangle)
        else:
            self.unsafe_boxes.append(self.best_rectangle)

        self.plot_results(self.anchor_points, additional_boxes_green = self.safe_boxes, additional_boxes_red = self.unsafe_boxes, display = False)

    def next_constraint(self):
        # computes next rectangle constraint
        # returns (new_constraint, new_covered_area)

        # reset
        self.max_size = 0
        self.max_area_safe = None
        self.best_rectangle = None
        self.best_anchor = None
        self.best_other_point
        self.best_anchor_points_for_dir = None
        self.best_pos_x = None
        self.best_pos_y = None

        # split samples into safe and bad
        (self.safe_samples, self.bad_samples) = sampling.split_samples(self.samples, self.threshold, self.safe_above_threshold)
        assert(len(self.safe_samples) + len(self.bad_samples) == len(self.samples))

        for (anchor_points_for_a_dir, pos_x, pos_y) in self.anchor_points:
            for anchor in anchor_points_for_a_dir:
                for point, value in self.samples.items():
                    point = Point(point)
                    # check if point lies in correct direction from anchor point
                    if not ((pos_x and point.x > anchor.x) or (not pos_x and point.x < anchor.x)):
                        continue;
                    if not ((pos_y and point.y > anchor.y) or (not pos_y and point.y < anchor.y)):
                        continue;

                    break_attempt = False
                    (min_x, max_x) = (point.x, anchor.x) if point.x < anchor.x else (anchor.x, point.x)
                    (min_y, max_y) = (point.y, anchor.y) if point.y < anchor.y else (anchor.y, point.y)
                    rectangle_test = box(min_x, min_y, max_x, max_y)
                    # check for intersection with existing rectangles
                    # TODO make more efficient
                    for rectangle2 in self.safe_boxes + self.unsafe_boxes:
                        if (self.intersects(rectangle_test, rectangle2)):
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
                    size = rectangle_test.area
                    if size > self.max_size and not break_attempt:
                        # check if nothing of other polarity is inbetween.
                        safe_area = (value < self.threshold and not self.safe_above_threshold) or (value >= self.threshold and self.safe_above_threshold)
                        other_points = self.bad_samples.keys() if safe_area else self.safe_samples.keys()
                        for point2 in other_points:
                            point2 = Point(point2)
                            if self.is_inside_rectangle(point2, rectangle_test):
                                # bad sample in safe area
                                break_attempt = True
                                break

                        if not break_attempt:
                            # can extend area
                            self.max_size = size
                            self.max_area_safe = safe_area
                            self.best_rectangle = rectangle_test
                            self.best_anchor = anchor
                            self.best_other_point = point
                            self.best_anchor_points_for_dir = anchor_points_for_a_dir
                            self.best_pos_x = pos_x
                            self.best_pos_y = pos_y

        if self.best_rectangle is not None and self.max_size > self.threshold_area:
            # plot result
            if self.max_area_safe:
                self.plot_results(self.anchor_points, additional_boxes_green = [self.best_rectangle], display = False)
            else:
                self.plot_results(self.anchor_points, additional_boxes_red = [self.best_rectangle], display = False)
            return (self.compute_constraint(self.best_rectangle), self.best_rectangle, self.max_area_safe)
        else:
            return None
