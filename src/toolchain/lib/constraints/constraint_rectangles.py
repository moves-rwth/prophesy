from constraint_generation import ConstraintGeneration, Anchor, Direction
from data.constraint import Constraint
from sympy.polys.polytools import Poly
from shapely.geometry import box, Point
from shapely import affinity
import sampling
import config

class ConstraintRectangles(ConstraintGeneration):

    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc):
        ConstraintGeneration.__init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc)

        self.anchor_points = [Anchor(Point(0, 0), Direction.NE),
                         Anchor(Point(1, 0), Direction.NW),
                         Anchor(Point(1, 1), Direction.SW),
                         Anchor(Point(0, 1), Direction.SE)]

        self.max_area_safe = None
        self.best_anchor = None
        self.best_rectangle = None
        self.best_other_point = None

        self.all_boxes = []

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
        pos_x, pos_y = self.best_anchor.pos
        self.best_other_point = (x2 if pos_x else x1, y2 if pos_y else y1)
        return (self.create_constraint(self.best_rectangle), self.best_rectangle, self.max_area_safe)

    def finalize_step(self, new_constraint):
        # remove contained anchors
        self.anchor_points.remove(self.best_anchor)
        anchors = self.anchor_points[:]
        for anchor in anchors:
            
            if anchor.pos.within(self.best_rectangle):
                self.anchor_points.remove(anchor)
            if anchor.pos.touches(self.best_rectangle):
                # Move anchor slightly in its own direction to test if it moves inside the rectangle
                # Little inaccuracy is OK, it just means extra work if it fails
                x = anchor.pos.x
                y = anchor.pos.y
                x += config.EPS if anchor.dir.value[0] else -config.EPS
                y += config.EPS if anchor.dir.value[1] else -config.EPS
                if Point(x,y).within(self.best_rectangle):
                    self.anchor_points.remove(anchor)

        # update anchor points for direction
        # Points to place new anchors at (+self.best_other_point)
        other_right = Point(self.best_other_point.x, self.best_anchor.pos.y)
        other_left = Point(self.best_anchor.pos.x, self.best_other_point.y)

        #TODO: Include the 'outer' point?
        #self.anchor_points.append(Anchor(self.best_other_point, self.best_anchor.dir))
        self.anchor_points.append(Anchor(other_right, self.best_anchor.dir))
        self.anchor_points.append(Anchor(other_left , self.best_anchor.dir))
        
        self.all_boxes.append(self.best_rectangle)

        self.plot_results(anchor_points=self.anchor_points)

    def next_constraint(self):
        # computes next rectangle constraint
        # returns (new_constraint, new_covered_area)

        # reset
        max_size = 0
        self.max_area_safe = None
        self.best_rectangle = None
        self.best_anchor = None
        self.best_other_point = None

        # split samples into safe and bad
        (self.safe_samples, self.bad_samples) = sampling.split_samples(self.samples, self.threshold, self.safe_above_threshold)
        assert(len(self.safe_samples) + len(self.bad_samples) == len(self.samples))

        for anchor in self.anchor_points:
            anchor_pos = anchor.pos
            pos_x, pos_y = anchor.dir.value
            for point, value in self.samples.items():
                point = Point(point)
                # check if point lies in correct direction from anchor point
                if not ((pos_x and point.x > anchor_pos.x) or (not pos_x and point.x < anchor_pos.x)):
                    continue;
                if not ((pos_y and point.y > anchor_pos.y) or (not pos_y and point.y < anchor_pos.y)):
                    continue;

                break_attempt = False
                (min_x, max_x) = (point.x, anchor_pos.x) if point.x < anchor_pos.x else (anchor_pos.x, point.x)
                (min_y, max_y) = (point.y, anchor_pos.y) if point.y < anchor_pos.y else (anchor_pos.y, point.y)
                rectangle_test = box(min_x, min_y, max_x, max_y)
                # check for intersection with existing rectangles
                # TODO make more efficient
                for rectangle2 in self.all_boxes:
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
                if size > max_size and not break_attempt and size > self.threshold_area:
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
                        max_size = size
                        self.max_area_safe = safe_area
                        self.best_rectangle = rectangle_test
                        self.best_anchor = anchor
                        self.best_other_point = point

                        # Plot candiate
                        self.plot_results(anchor_points=self.anchor_points, poly_blue = [self.best_rectangle], display = False)

        if self.best_rectangle is not None:
            return (self.compute_constraint(self.best_rectangle), self.best_rectangle, self.max_area_safe)
        else:
            return None
