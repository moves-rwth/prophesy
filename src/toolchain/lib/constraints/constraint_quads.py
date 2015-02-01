from constraint_generation import ConstraintGeneration
from shapely.geometry import box, Point

class Quad(object):
    def __init__(self, origin, size):
        self.origin = origin
        self.size = size
        self.poly = box(self.origin.x, self.origin.y, self.origin.x+self.size, self.origin.y+self.size)

    def split(self):
        if self.width < 0.01:
            return None
        return [Quad(Point(self.origin.x, self.origin.y),                         self.self.size/2),
                Quad(Point(self.origin.x+self.size/2, self.origin.y),             self.self.size/2),
                Quad(Point(self.origin.x, self.origin.y+self.size/2),             self.self.size/2),
                Quad(Point(self.origin.x+self.size/2, self.origin.y+self.size/2), self.self.size/2)]

class ConstraintQuads(ConstraintGeneration):
    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc):
        super().__init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc)

        self.quads = []
        # Number of consecutive recursive splits() maximum
        self.check_depth = 64
        
        # Setup initial quad
        quad = Quad(Point(0,0), 1.0)
        quadsamples = []
        for pt, v in samples:
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

    def change_current_constraint(self):
        # TODO: Implement
        # Split quad and try again
        pass

    def check_quad(self, quad_elem, depth = 0):
        """Check if given quad can be assumed safe or bad based on
        known samples. If samples are mixed, split the quad and retry.
        Resulting quads are added to self.quads"""
        if depth == self.check_depth:
            assert False, "Too deep"
            self.quads.append(quad_elem)
            return
        
        quad, samples = quad_elem
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
        
        # Samples are mixed
        newquads = quad.split()
        newsamples = [[]] * len(newquads)
        newpairs = zip(newquads, newsamples)

        for pt, safe in samples.items():
            for newquad, newsamples in newpairs:
                mapped = False
                if newquad.poly.intersects(pt):
                    mapped = True
                    newsamples.append((pt, safe))
                assert mapped, "Unmapped sample {},{} {}".format(pt.x, pt.y, safe)
        #self.quads += newpairs
        for pair in newpairs:
            self.check_quad(pair, depth+1)

    def reject_constraint(self, constraint, safe, sample):
        # New sample, add it to current quad, and check it
        # Also remove failed quad
        self.quads[0][1].append((Point(sample[0]), not safe))
        self.check_quad(self.quads[0])
        self.quads = self.quads[1:]

    def accept_constraint(self, constraint, safe):
        # Done with the quad
        self.quads = self.quads[1:]

    def next_constraint(self):
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
