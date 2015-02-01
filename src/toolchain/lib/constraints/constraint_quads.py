from constraint_generation import ConstraintGeneration
from shapely.geometry import box, Point
import sampling
import config

class Quad(object):
    def __init__(self, origin, size):
        self.origin = origin
        self.size = size

    def split(self):
        if self.width < 0.01:
            return None
        return [Quad(Point(self.origin.x, self.origin.y),                         self.self.size/2),
                Quad(Point(self.origin.x+self.size/2, self.origin.y),             self.self.size/2),
                Quad(Point(self.origin.x, self.origin.y+self.size/2),             self.self.size/2),
                Quad(Point(self.origin.x+self.size/2, self.origin.y+self.size/2), self.self.size/2)]

    def as_poly(self):
        return box(self.origin.x, self.origin.y, self.origin.x+self.size, self.origin.y+self.size)

class ConstraintQuads(ConstraintGeneration):

    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc):
        super().__init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc)

        self.quads = [Quad(Point(0,0), 1.0)]
        self.best_quad = None
        self.best_quad_safe = True

    def is_inside_rectangle(self, point, rectangle):
        # checks if the point lies in the rectangle
        return point.within(rectangle) or point.touches(rectangle)

    def intersects(self, rectangle1, rectangle2):
        # checks if rectangles intersect, touching is okay
        return rectangle1.intersects(rectangle2) and not rectangle1.touches(rectangle2)

    def create_quad_constraint(self, quad):
        box = box(quad.origin.x, quad.origin.y, quad.origin.x+quad.size, quad.origin.y+quad.size)
        return self.compute_constraint(box)

    def change_current_constraint(self):
        new_quads = self.best_quad.split()
        if new_quads is None:
            return None
        self.best_quad = new_quads[0]
        self.best_quad_safe = True
        self.quads.append(new_quads[1:])

    def finalize_step(self, new_constraint):
        self.best_quad = None
        self.best_quad_safe = True

    def next_constraint(self):
        if self.best_quad and self.best_quad_safe:
            self.best_quad_safe = False
            poly = self.best_quad.as_poly()
            return (self.compute_constraint(poly), poly, self.best_quad_safe)

        # TODO: Make everything logical
        self.best_quad = self.quads[0]
        self.best_quad_safe = True
        self.quads = self.quads[1:]

        poly = self.best_quad.as_poly()
        return (self.compute_constraint(poly), poly, self.best_quad_safe)