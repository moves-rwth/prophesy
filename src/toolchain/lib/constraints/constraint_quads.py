from constraint_generation import ConstraintGeneration
from shapely.geometry import box, Point
from functools import total_ordering

@total_ordering
class Quad(object):
    def __init__(self, origin, size):
        self.origin = origin
        self.size = size
        self.poly = box(self.origin.x, self.origin.y, self.origin.x+self.size, self.origin.y+self.size)

    def split(self):
        if self.size < 1.0/(2**6):
            return None
        return [Quad(Point(self.origin.x, self.origin.y),                         self.size/2),
                Quad(Point(self.origin.x+self.size/2, self.origin.y),             self.size/2),
                Quad(Point(self.origin.x, self.origin.y+self.size/2),             self.size/2),
                Quad(Point(self.origin.x+self.size/2, self.origin.y+self.size/2), self.size/2)]

    def __repr__(self):
        return "Quad(Point({},{}), {})".format(self.origin.x, self.origin.y, self.size)

    def __str__(self):
        return str(list(self.poly.exterior.coords))

    def __hash__(self):
        return hash(self.origin) ^ hash(self.size)

    def __eq__(self, other):
        return self.origin == other.origin and self.size == other.size

    def __lt__(self, other):
        if self.size < other.size:
            return True
        return self.origin.x < other.origin.x

class ConstraintQuads(ConstraintGeneration):
    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc):
        super().__init__(samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc)

        self.quads = []
        # Number of consecutive recursive splits() maximum
        self.check_depth = 64
        
        # Setup initial quad
        quad = Quad(Point(0,0), 1.0)
        quadsamples = []
        for pt, v in samples.items():
            safe = (v >= self.threshold) == self.safe_above_threshold
            quadsamples.append((Point(pt), safe))
        self.check_quad((quad, quadsamples))

    def is_inside_rectangle(self, point, rectangle):
        # checks if the point lies in the rectangle
        return point.within(rectangle) or point.touches(rectangle)

    def intersects(self, rectangle1, rectangle2):
        # checks if rectangles intersect, touching is okay
        return rectangle1.intersects(rectangle2) and not rectangle1.touches(rectangle2)

    def create_quad_constraint(self, quad):
        box = box(quad.origin.x, quad.origin.y, quad.origin.x+quad.size, quad.origin.y+quad.size)
        return self.compute_constraint(box)

    def split_quad(self, quad_elem):
        (quad, quadsamples) = quad_elem
        newquads = quad.split()
        if newquads is None:
            return
        newsamples = [[] for _ in newquads]
        newelems = [i for i in zip(newquads, newsamples)]

        for pt, safe in quadsamples:
            mapped = False
            for newquad, newsamples in newelems:
                #print("Intersect {} {} : {}".format((pt.x,pt.y), newquad, newquad.poly.intersects(pt)))
                if newquad.poly.intersects(pt):
                    mapped = True
                    newsamples.append((pt, safe))
            assert mapped, "Unmapped sample {},{} {}".format(pt.x, pt.y, safe)
        return newelems

    def check_quad(self, quad_elem, depth = 0):
        """Check if given quad can be assumed safe or bad based on
        known samples. If samples are mixed, split the quad and retry.
        Resulting quads are added to self.quads"""
        if depth == self.check_depth:
            assert False, "Too deep"
            self.quads.append(quad_elem)
            return

        samples = quad_elem[1]
        if len(samples) <= 1:
            self.quads.append(quad_elem)
            return
        if all([sample[1] for sample in samples]):
            # All safe
            self.quads.append(quad_elem)
            return
        elif all([not sample[1] for sample in samples]):
            # All bad
            self.quads.append(quad_elem)
            return

        newelems = self.split_quad(quad_elem)
        if newelems is None:
            return None
        #self.quads += newpairs
        for pair in newelems:
            self.check_quad(pair, depth+1)

    def fail_constraint(self, constraint, safe):
        # Split quad and try again
        quadelem = self.quads[0]
        newelems = self.split_quad(quadelem)
        # Currently no need to check it,
        # failure ony applies for quad that was already consistent
        self.quads = self.quads[1:]
        if newelems is not None:
            self.quads = newelems + self.quads
        if len(self.quads) == 0:
            return None
        self.quads.sort(reverse=True)
        quad = self.quads[0][0]
        return (self.compute_constraint(quad.poly), quad.poly, safe)

    def reject_constraint(self, constraint, safe, sample):
        # New sample, add it to current quad, and check it
        # Also remove failed quad
        self.quads[0][1].append((Point(sample[0]), not safe))
        self.check_quad(self.quads[0])
        self.quads = self.quads[1:]
        self.quads.sort(reverse=True)

    def accept_constraint(self, constraint, safe):
        # Done with the quad
        self.quads = self.quads[1:]

    def next_constraint(self):
        if len(self.quads) == 0:
            return None

        quad, quadsamples = self.quads[0]
        constraint = self.compute_constraint(quad.poly)

        if len(quadsamples) == 0:
            # Assume safe at first (rather arbitrary)
            return (constraint, quad.poly, True)
        if all([sample[1] for sample in quadsamples]):
            # All safe
            return (constraint, quad.poly, True)
        elif all([not sample[1] for sample in quadsamples]):
            # All bad
            return (constraint, quad.poly, False)

        assert False, "A mixed quad was left in the quad queue, wut"
