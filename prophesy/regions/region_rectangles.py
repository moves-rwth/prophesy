from prophesy.data.samples import split_samples, ParameterInstantiation
from prophesy.regions.region_generation import RegionGenerator
from shapely.geometry import box
from shapely import affinity
from prophesy.config import configuration
import shapely.geometry.point
import prophesy.data.point
from prophesy.adapter.pycarl import Rational


from enum import Enum
from numpy import array

#TODO: This class needs to be rewritten to use HyperRectangles


class Direction(Enum):
    """The four intercardinal directions ('North-East' etc.) as boolean
    2-tuples.

    The first entry corresponds to the West-East axis (`True` being
    East), the second to North-South (`true` being North)."""
    NE = (True, True)
    SE = (True, False)
    NW = (False, True)
    SW = (False, False)

    @classmethod
    def from_bool(cls, pos_x, pos_y):
        """
        @param pos_x Boolean indicating of x axis should be positive or negative
        @param pos_y Boolean indicating of y axis should be positive or negative
        @return Direction
        """
        if pos_x:
            if pos_y:
                return cls.NE
            else:
                return cls.SE
        else:
            if pos_y:
                return cls.NW
            else:
                return cls.SW

    def to_vector(self):
        """Return vector indicating the direction
        @return numpy.array, 2D
        """
        vector = {Direction.NE: array([ 1,  1]),
                  Direction.SE: array([ 1, -1]),
                  Direction.NW: array([-1,  1]),
                  Direction.SW: array([-1, -1])}
        return vector[self]


class Anchor:
    """Represents an 'Anchor' point, used to define certain locations useful,
    for instance to iniate growing rectangles from
    """
    def __init__(self, pos, direction, safe):
        """
        @param pos shapely Point
        @param direction Direction
        @param safe Boolean to indiavte if Anchor is considered in a safe area
        """
        self.pos = pos
        self.dir = direction
        self.safe = safe

    def __hash__(self, *args, **kwargs):
        return hash(self.pos) ^ hash(self.dir)

    def __eq__(self, other):
        if not isinstance(other, Anchor):
            return False
        if self.pos == other.pos and self.dir == other.dir:
            assert(self.safe == other.safe)
            return True
        else:
            return False

    def __str__(self):
        return "({}, {}) {} (Safe: {})".format(self.pos.x, self.pos.y, self.dir, self.safe)

class ConstraintRectangles(RegionGenerator):

    def __init__(self, samples, parameters, threshold, threshold_area, _smt2interface, _ratfunc):
        RegionGenerator.__init__(self, samples, parameters, threshold, threshold_area, _smt2interface, _ratfunc)

        self.x_min = parameters[0].interval.left_bound()
        self.x_max = parameters[0].interval.right_bound()
        self.y_min = parameters[1].interval.left_bound()
        self.y_max = parameters[1].interval.right_bound()

        self.anchor_points = []

        # Add anchors CCW
        for pt, direction in [
                ((self.x_min, self.y_min), Direction.NE),
                ((self.x_max, self.y_min), Direction.NW),
                ((self.x_max, self.y_max), Direction.SW),
                ((self.x_min, self.y_max), Direction.SE)]:
            # initialy safe flag for anchors properly
            pt2 = list(pt)
            if pt2[0] == 0:
                pt2[0] = Rational(1)/Rational(1e6)
            if pt2[0] == 1:
                pt2[0] = Rational(999999)/Rational(1e6)
            if pt2[1] == 0:
                pt2[1] = Rational(1)/Rational(1e6)
            if pt2[1] == 1:
                pt2[1] = Rational(999999)/Rational(1e6)
            sp = ParameterInstantiation.from_point(prophesy.data.point.Point(*pt2), self.parameters.get_variable_order())
            value = self.ratfunc.evaluate(sp)
            if value >= self.threshold:
                pt_safe = True
            else:
                pt_safe = False
            self.anchor_points.append(Anchor(shapely.geometry.point.Point(pt2), direction, pt_safe))

        self.best_anchor = None
        self.best_rectangle = None
        self.best_other_point = None
        self.next_rectangles = []

        self.all_boxes = []

    def plot_candidate(self):
        self.plot_results(anchor_points=self.anchor_points, poly_blue=[self.best_rectangle], display=False)

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
        old_rectangle = self.best_rectangle
        old_other_point = self.best_other_point
        self.best_rectangle = affinity.scale(self.best_rectangle, xfact=0.5, yfact=0.5, origin=(self.best_anchor.pos.x, self.best_anchor.pos.y))
        if self.best_rectangle.area < self.threshold_area:
            # Discard rectangle and try other one by removing anchor
            # TODO better solution?
            try:
                self.anchor_points.remove(self.best_anchor)
            except ValueError:
                pass
            return self.next_constraint()

        (x1, y1, x2, y2) = self.best_rectangle.bounds
        pos_x, pos_y = self.best_anchor.dir.value
        self.best_other_point = shapely.geometry.point.Point(x2 if pos_x else x1, y2 if pos_y else y1)

        # remember discarded part of rectangle for future constaraints
        anchor1_pt = shapely.geometry.point.Point(self.best_anchor.pos.x, self.best_other_point.y)
        anchor2_pt = shapely.geometry.point.Point(self.best_other_point.x, self.best_anchor.pos.y)
        anchor3_pt = shapely.geometry.point.Point(self.best_other_point)
        anchor1 = Anchor(anchor1_pt, self.best_anchor.dir, self.best_anchor.safe)
        anchor2 = Anchor(anchor2_pt, self.best_anchor.dir, self.best_anchor.safe)
        anchor3 = Anchor(anchor3_pt, self.best_anchor.dir, self.best_anchor.safe)
        rectangle1 = affinity.scale(old_rectangle, xfact=0.5, yfact=0.5, origin=(self.best_anchor.pos.x, old_other_point.y))
        rectangle2 = affinity.scale(old_rectangle, xfact=0.5, yfact=0.5, origin=(old_other_point.x, self.best_anchor.pos.y))
        rectangle3 = affinity.scale(old_rectangle, xfact=0.5, yfact=0.5, origin=(old_other_point.x, old_other_point.y))
        self.next_rectangles += [(rectangle1, anchor1), (rectangle2, anchor2), (rectangle3, anchor3)]

        return self.best_rectangle, self.best_anchor.safe

    def reject_constraint(self, constraint, safe, sample):
        pass

    def accept_constraint(self, constraint, safe):
        # remove contained anchors
        try:
            self.anchor_points.remove(self.best_anchor)
        except ValueError:
            pass
        anchors = self.anchor_points[:]
        for anchor in anchors:
            if anchor.pos.within(self.best_rectangle):
                self.anchor_points.remove(anchor)
            if anchor.pos.touches(self.best_rectangle):
                # Move anchor slightly in its own direction to test if it moves inside the rectangle
                # Little inaccuracy is OK, it just means extra work if it fails
                x = anchor.pos.x
                y = anchor.pos.y
                x += configuration.get_regions_precision() if anchor.dir.value[0] else -configuration.get_regions_precision()
                x += configuration.get_regions_precision() if anchor.dir.value[1] else -configuration.get_regions_precision()
                if shapely.geometry.point.Point(x, y).within(self.best_rectangle):
                    self.anchor_points.remove(anchor)

        # update anchor points for direction
        # Points to place new anchors at (+self.best_other_point)
        other_right = shapely.geometry.point.Point(self.best_other_point.x, self.best_anchor.pos.y)
        other_left = shapely.geometry.point.Point(self.best_anchor.pos.x, self.best_other_point.y)

        #TODO: Include the 'outer' point?
        #self.anchor_points.append(Anchor(self.best_other_point, self.best_anchor.dir))
        self.anchor_points.append(Anchor(other_right, self.best_anchor.dir, safe))
        self.anchor_points.append(Anchor(other_left , self.best_anchor.dir, safe))

        self.all_boxes.append(self.best_rectangle)

    def next_constraint(self):
        # computes next rectangle constraint
        # returns (new_constraint, new_covered_area)

        # check if rectangle is in queue to process next
        if len(self.next_rectangles) > 0:
            (next_rectangle, anchor) = self.next_rectangles.pop(0)
            self.best_rectangle = next_rectangle
            self.max_area_safe = anchor.safe
            self.best_anchor = anchor
            (x1, y1, x2, y2) = self.best_rectangle.bounds
            pos_x, pos_y = self.best_anchor.dir.value
            self.best_other_point = shapely.geometry.point.Point(x2 if pos_x else x1, y2 if pos_y else y1)
            return  self.best_rectangle, self.best_anchor.safe

        # "normal" case where there is no rectangle in the queue
        # reset
        self.best_rectangle = None
        self.best_anchor = None
        self.best_other_point = None

        # split samples into safe and bad
        (safe_samples, bad_samples) = split_samples(self.samples, self.threshold)

        for anchor in self.anchor_points:
            anchor_pos = anchor.pos

            pos_x, pos_y = anchor.dir.value
            for point, value in safe_samples.items() if anchor.safe else bad_samples.items():
                # check if point lies in correct direction from anchor point
                if not ((pos_x and point.x > anchor_pos.x) or (not pos_x and point.x < anchor_pos.x)):
                    continue
                if not ((pos_y and point.y > anchor_pos.y) or (not pos_y and point.y < anchor_pos.y)):
                    continue

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
                    safe_area = value >= self.threshold
                    anchor.safe = safe_area
                    other_points = bad_samples.keys() if safe_area else safe_samples.keys()
                    for point2 in other_points:
                        point2 = shapely.geometry.point.Point(point2)
                        if self.is_inside_polygon(point2, rectangle):
                            # wrong sample in covered area
                            break_attempt = True
                            break

                    if not break_attempt:
                        # can extend area
                        self.best_rectangle = rectangle
                        self.best_anchor = anchor
                        self.best_other_point = point

        if self.best_rectangle is not None:
            return self.best_rectangle, self.best_anchor.safe
        else:
            return None

    def plot_results(self, *args, **kwargs):
        if not self.plot:
            return
        kwargs['anchor_points'] = self.anchor_points
        super().plot_results(*args, **kwargs)
