from constraint_generation import ConstraintGeneration, Anchor, Direction
from shapely.geometry import box, Point
from shapely import affinity
import sampling
import config

class ConstraintRectangles(ConstraintGeneration):

    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc):
        ConstraintGeneration.__init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc)

        self.anchor_points = []
        for pt, dir in [((0, 0), Direction.NE), ((1, 0), Direction.NW), ((1, 1), Direction.SW), ((0, 1), Direction.SE)]:
            value = self.ratfunc.eval({x:y for x,y in zip(self.parameters, pt)}).evalf()
            if (self.safe_above_threshold and value >= self.threshold) or (not self.safe_above_threshold and value < self.threshold):
                pt_safe = True
            else:
                pt_safe = False
            self.anchor_points.append(Anchor(Point(pt), dir, pt_safe))

        self.max_area_safe = None
        self.best_anchor = None
        self.best_rectangle = None
        self.best_other_point = None

        self.all_boxes = []

    def plot_candidate(self):
        self.plot_results(anchor_points=self.anchor_points, poly_blue = [self.best_rectangle], display = False)

    def refine_with_intersections(self, polygon):
        # check for intersection with existing rectangles
        # TODO make more efficient
        for rectangle2 in self.all_boxes:
            if self.intersects(polygon, rectangle2):
                # TODO set largest part of remaining difference as new rectangle 
                #polygon = polygon.difference(rectangle2)
                return None
        return polygon

    def fail_constraint(self, constraint, safe):
        # change current constraint to avoid memout in smt
        # returns (new_constraint, new_covered_area, area_safe)

        # scale rectangle by factor 0.5
        self.best_rectangle = affinity.scale(self.best_rectangle, xfact=0.5, yfact=0.5, origin=self.best_anchor.pos)
        if self.best_rectangle.area < self.threshold_area:
            # Discard rectangle and try other one by removing anchor
            # TODO better solution?
            self.anchor_points.remove(self.best_anchor)
            return self.next_constraint()

        (x1, y1, x2, y2) = self.best_rectangle.bounds
        pos_x, pos_y = self.best_anchor.dir.value
        self.best_other_point = Point(x2 if pos_x else x1, y2 if pos_y else y1)
        return (self.compute_constraint(self.best_rectangle), self.best_rectangle, self.max_area_safe)

    def reject_constraint(self, constraint, safe, sample):
        pass

    def accept_constraint(self, constraint, safe):
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
        self.anchor_points.append(Anchor(other_right, self.best_anchor.dir, safe))
        self.anchor_points.append(Anchor(other_left , self.best_anchor.dir, safe))

        self.all_boxes.append(self.best_rectangle)

    def next_constraint(self):
        # computes next rectangle constraint
        # returns (new_constraint, new_covered_area)

        # reset
        self.max_area_safe = None
        self.best_rectangle = None
        self.best_anchor = None
        self.best_other_point = None

        # split samples into safe and bad
        (safe_samples, bad_samples) = sampling.split_samples(self.samples, self.threshold, self.safe_above_threshold)

        for anchor in self.anchor_points:
            anchor_pos = anchor.pos

            pos_x, pos_y = anchor.dir.value
            for point, value in safe_samples.items() if anchor.safe else bad_samples.items():
                point = Point(point)
                # check if point lies in correct direction from anchor point
                if not ((pos_x and point.x > anchor_pos.x) or (not pos_x and point.x < anchor_pos.x)):
                    continue;
                if not ((pos_y and point.y > anchor_pos.y) or (not pos_y and point.y < anchor_pos.y)):
                    continue;

                break_attempt = False
                (min_x, max_x) = (point.x, anchor_pos.x) if point.x < anchor_pos.x else (anchor_pos.x, point.x)
                (min_y, max_y) = (point.y, anchor_pos.y) if point.y < anchor_pos.y else (anchor_pos.y, point.y)
                rectangle = box(min_x, min_y, max_x, max_y)
                rectangle = self.refine_with_intersections(rectangle)
                if rectangle is None:
                    continue

                # choose largest rectangle
                if self.best_rectangle is None or (rectangle.area > self.best_rectangle.area and rectangle.area > self.threshold_area):
                    # check if nothing of other polarity is inbetween.
                    safe_area = (value < self.threshold and not self.safe_above_threshold) or (value >= self.threshold and self.safe_above_threshold)
                    other_points = bad_samples.keys() if safe_area else safe_samples.keys()
                    for point2 in other_points:
                        point2 = Point(point2)
                        if self.is_inside_polygon(point2, rectangle):
                            # wrong sample in covered area
                            break_attempt = True
                            break

                    if not break_attempt:
                        # can extend area
                        self.max_area_safe = safe_area
                        self.best_rectangle = rectangle
                        self.best_anchor = anchor
                        self.best_other_point = point

        if self.best_rectangle is not None:
            return (self.compute_constraint(self.best_rectangle), self.best_rectangle, self.max_area_safe)
        else:
            return None
