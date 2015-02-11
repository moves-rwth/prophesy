import tempfile
import time
import os
import smt.smt
from output.plot import Plot
from abc import ABCMeta, abstractmethod
# needed for pdf merging for debugging
from subprocess import call
from config import PLOT_FILES_DIR, EPS
from util import ensure_dir_exists
from data.constraint import Constraint, ComplexConstraint
from sympy.polys.polytools import Poly
from numpy import array
import shutil
from shapely.geometry.polygon import Polygon, orient, LinearRing
from enum import Enum

class Direction(Enum):
    NE = (True, True)
    SE = (True, False)
    NW = (False, True)
    SW = (False, False)

    @classmethod
    def from_bool(cls, pos_x, pos_y):
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
        vector = {  Direction.NE: array([ 1,  1]),
                    Direction.SE: array([ 1, -1]),
                    Direction.NW: array([-1,  1]),
                    Direction.SW: array([-1, -1])}
        return vector[self]

class Anchor(object):
    def __init__(self, pos, dir, safe):
        self.pos = pos
        self.dir = dir
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

class ConstraintGeneration(object):
    """A generator for constraints. This class acts as an iterable that
    generates new constraints (or counterexamples) until the search space is exhausted
    (which possibly never happens)"""
    __metaclass__ = ABCMeta

    def __init__(self, samples, parameters, threshold, threshold_area, _smt2interface, _ratfunc):
        if len(parameters) != 2:
            raise NotImplementedError

        self.samples = samples.copy()
        self.parameters = parameters
        self.threshold = threshold
        self.threshold_area = threshold_area

        self.smt2interface = _smt2interface
        self.ratfunc = _ratfunc

        self.benchmark_output = []
        # Stores all constraints as triple ([constraint], polygon representation, bad/safe)
        self.all_constraints = []
        self.safe_polys = []
        self.bad_polys = []
        self.new_samples = {}

        self.plot = True
        self.first_pdf = True
        ensure_dir_exists(PLOT_FILES_DIR)
        (_, self.result_file) = tempfile.mkstemp(suffix = ".pdf", prefix = "result_", dir = PLOT_FILES_DIR)

    def __iter__(self):
        # Prime the generator
        return next(self)

    def __next__(self):
        with self.smt2interface as smtcontext:
            # initial constraints
            for param in self.parameters:
                # add constraints 0 <= param <= 1
                smtcontext.assert_constraint(Constraint(Poly(param, self.parameters), ">=", self.parameters))
                smtcontext.assert_constraint(Constraint(Poly(param - 1, self.parameters), "<=", self.parameters))

            # get next constraint depending on algorithm
            result_constraint = self.next_constraint()
            while result_constraint is not None:
                (new_constraint, polygon, area_safe) = result_constraint
                result = self.analyze_constraint(new_constraint, polygon, area_safe)
                if result is None:
                    return # End of generator
                yield result

                # get next constraint depending on algorithm
                result_constraint = self.next_constraint()
        return # End of generator

    def add_pdf(self, name):
        """Adds pdf with name to result.pdf in tmp directory
        first indicates if resultfile exists already"""
        if self.first_pdf:
            self.first_pdf = False
            shutil.copyfile(name, self.result_file)
            print("Plot file located at {0}".format(self.result_file))
        else:
            (_, result_tmp_file) = tempfile.mkstemp(".pdf", dir = PLOT_FILES_DIR)
            call(["pdfunite", self.result_file, name, result_tmp_file])
            try:
                shutil.move(result_tmp_file, self.result_file)
            except:
                os.unlink(result_tmp_file)

    def compute_constraint(self, polygon):
        """Compute constraints from polygon (Polygon, LineString or LinearRing)
        Area will be considered at the rhs (ccw) of line segments
        Polygon must be convex
        returns single (Complex)Constraint describing the polygon
        """
        if isinstance(polygon, LinearRing):
            # Convert to polygon so it can be oriented
            polygon = Polygon(polygon)

        if isinstance(polygon, Polygon):
            assert len(list(polygon.interiors)) == 0
            polygon = orient(polygon, sign = 1.0)
            polygon = polygon.exterior
        points = list(polygon.coords)
        assert len(points) >= 2

        constraint = None
        # Calculate half-plane for each pair of points
        # http://math.stackexchange.com/questions/82151/find-the-equation-of-the-plane-passing-through-a-point-and-a-vector-orthogonal
        for p1, p2 in zip(points[:-1], points[1:]):
            # Get vector direction (parallel to hyperplane)
            dvec = tuple([c2 - c1 for c1, c2 in zip(p1, p2)])
            # Make vector orthogonal to hyperplane
            # NOTE: rotate clockwise
            # TODO: 2D only
            dvec = (dvec[1], -dvec[0])

            # Constant is dot-product of directional vector and origin
            c = sum([c1 * c2 for c1, c2 in zip(dvec, p1)])
            # Construct polynomial for line
            poly = Poly(-c, self.parameters)
            for parameter, coefficient in zip(self.parameters, dvec):
                if coefficient != 0:
                    poly = Poly(poly + parameter * coefficient, self.parameters)

            # TODO: '<=' as polygon is CCW oriented, not sure if this applies to n-dimen
            new_constraint = Constraint(poly, "<=", self.parameters)
            if constraint is None:
                constraint = new_constraint
            else:
                constraint = constraint & new_constraint

        # print("constraint: {0}".format(constraint))
        return constraint

    @classmethod
    def is_point_fulfilling_constraint(cls, pt, constraint):
        """Check wether the given point is satisfied by the constraints
        (i.e. is contained by it)"""
        if isinstance(constraint, ComplexConstraint):
            if constraint.operator == "or":
                return any([cls.is_point_fulfilling_constraint(pt, sub_constraint) for sub_constraint in constraint.constraints])
            elif constraint.operator == "and":
                return all([cls.is_point_fulfilling_constraint(pt, sub_constraint) for sub_constraint in constraint.constraints])
            else:
                assert False, "Unknown constraint operator {}".format(constraint.operator)

        pol = constraint.polynomial.eval({x:y for x, y in zip(constraint.symbols, pt)}).evalf()

        if constraint.relation == "=":
            return abs(pol) < EPS
        elif constraint.relation == "<":
            return pol < 0
        elif constraint.relation == ">":
            return pol > 0
        elif constraint.relation == "<=":
            return pol <= 0
        elif constraint.relation == ">=":
            return pol >= 0
        elif constraint.relation == "<>":
            return abs(pol) > EPS

    @staticmethod
    def print_benchmark_output(benchmark_output):
        i = 1
        print("no.  result   time  tot. time   area  tot. area")
        total_sec = 0
        total_area = 0
        for benchmark in benchmark_output:
            total_sec = total_sec + benchmark[1]
            if benchmark[0] == smt.smt.Answer.unsat:
                total_area = total_area + benchmark[2]
            print("{:3}".format(i) + "   {:>6s}".format(benchmark[0].name) + "  {:5.2f}".format(benchmark[1]) + "     {:6.2f}".format(total_sec) + "  {:4.3f}".format(benchmark[2]) + "      {:4.3f}".format(total_area))
            i = i + 1

    def plot_candidate(self):
        pass

    def plot_results(self, *args, **kwargs):
        if not self.plot:
            return
        #Extend arguments
        poly_green = kwargs.get('poly_green')
        if poly_green is None:
            poly_green = []
        kwargs['poly_green'] = poly_green + self.safe_polys
        poly_red = kwargs.get('poly_red')
        if poly_red is None:
            poly_red = []
        kwargs['poly_red'] = poly_red + self.bad_polys

        #Split samples appropriately
        samples_green = [pt for pt, v in self.samples.items() if v >= self.threshold]
        samples_red = [pt for pt, v in self.samples.items() if v < self.threshold]

        (_, result_tmp_file) = tempfile.mkstemp(".pdf", dir = PLOT_FILES_DIR)
        Plot.plot_results(parameters = self.parameters,
                          samples_green = samples_green,
                          samples_red = samples_red,
                          path_to_save = result_tmp_file,
                          *args, **kwargs)
        self.add_pdf(result_tmp_file)
        os.unlink(result_tmp_file)

    def is_inside_polygon(self, point, polygon):
        # checks if the point lies inside the polygon
        return point.within(polygon) or point.touches(polygon)

    def intersects(self, polygon1, polygon2):
        """checks if two polygons intersect, touching is okay"""
        #TODO first check bounding boxes?
        return polygon1.intersects(polygon2) and not polygon1.touches(polygon2)

    @abstractmethod
    def refine_with_intersections(self, polygon):
        """Compute the intersections of the polygon with the existing ones
        and refine it by getting the difference
        returns the refined polygon"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def next_constraint(self):
        """Generate a new set of constraints ([constraints], area, area_safe),
        where [constraints] is a list of Constraint, area is a polygon representation of the new area
        and area_safe indicated whether the area should be determined safe (or not)"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def fail_constraint(self, constraint, safe):
        """Update current set of constraints, usually to avoid mem or time out.
        Returns same as next_constraint"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def reject_constraint(self, constraint, safe, sample):
        """Called for a constraint that is rejected (sample found).
        sample is tuple((x,y), value)"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def accept_constraint(self, constraint, safe):
        """Called for a constraint that is accepted (i.e. unsat)"""
        raise NotImplementedError("Abstract parent method")

    def analyze_constraint(self, constraint, polygon, safe):
        """Extends the current area by using the new polygon
        constraints are the newly added constraints for the polygon
        polygon marks the new area to cover
        safe indicates whether the area is safe or bad
        returns tuple (valid constraint, polygon/counterexample point)
        if constraint is valid the tuple  is (True, polygon added)
        if constraint is invalid the tuple is (False, point as counterexample)
        """
        smt_successful = False
        smt_model = None

        self.plot_candidate()

        while not smt_successful:
            # check constraint with smt
            with self.smt2interface as smt_context:
                #print("Checking constraint {}".format(constraint))
                smt_context.assert_constraint(constraint)

                smt_context.set_guard("safe", not safe)
                smt_context.set_guard("bad", safe)
                #print("Calling smt solver")
                start = time.time()
                checkresult = smt_context.check()
                duration = time.time() - start
                #print("Call took {0} seconds".format(duration))
                self.benchmark_output.append((checkresult, duration, polygon.area))
                #self.print_benchmark_output(self.benchmark_output)
                if not checkresult in [smt.smt.Answer.sat, smt.smt.Answer.unsat]:
                    # smt call not finished -> change constraint to make it better computable
                    # TODO what to do in GUI?
                    #print("{}: Change constraint for better computation".format(checkresult))
                    result_update = self.fail_constraint(constraint, safe)
                    if result_update == None:
                        break
                    self.plot_candidate()
                    (constraint, polygon, safe) = result_update
                else:
                    smt_successful = True
                    if checkresult == smt.smt.Answer.sat:
                        smt_model = smt_context.get_model()
                    break

        if checkresult == smt.smt.Answer.unsat:
            # remove unnecessary samples which are covered already by constraints
            for pt in list(self.samples.keys()):
                if self.is_point_fulfilling_constraint(pt, constraint):
                    del self.samples[pt]

            # update everything in the algorithm according to correct new area
            self.accept_constraint(constraint, safe)
            return (True, (constraint, polygon, safe))
        elif checkresult == smt.smt.Answer.sat:
            # add new point as counter example to existing constraints
            modelPoint = ()
            for p in self.parameters:
                if p.name in smt_model:
                    modelPoint = modelPoint + (smt_model[p.name],)
                else:
                    # if parameter is undefined set as 0.5
                    modelPoint = modelPoint + (0.5,)
                    smt_model[p.name] = 0.5
            value = self.ratfunc.subs(smt_model.items()).evalf()
            self.reject_constraint(constraint, safe, (modelPoint, value))
            return (False, (modelPoint, value))
        else:
            # SMT failed completely
            return None

    def generate_constraints(self, max_iter = -1, max_area = 1.0):
        """Iteratively generates new constraints, heuristically, attempting to
        find the largest safe or unsafe area
        max_iter: Number of constraints to generate/check at most (not counting SMT failures),
        -1 for unbounded"""
        if max_iter == 0:
            return (self.safe_polys, self.bad_polys, self.new_samples)

        for result in self:
            (unsat, data) = result
            if unsat:
                self.all_constraints.append(data)
                (constraint, poly, safe) = data
                if safe:
                    self.safe_polys.append(poly)
                else:
                    self.bad_polys.append(poly)
                print("added new polygon {0} with constraint: {1}".format(poly, constraint))
            else:
                (point, value) = data
                self.new_samples[point] = value
                print("added new sample {0} with value {1}".format(point, value))
            
            area_sum = sum([benchmark[2] for benchmark in self.benchmark_output if benchmark[0] == smt.smt.Answer.unsat])
            if area_sum > max_area:
                break
            max_iter -= 1
            if max_iter == 0:
                break

            # Plot intermediate result
            if len(self.all_constraints) % 20 == 0:
                self.plot_results(display = False)

        # Plot the final outcome
        if self.plot:
            self.plot_results(display = False)
            print("Generation complete, plot located at {0}".format(self.result_file))
        self.print_benchmark_output(self.benchmark_output)

        return (self.safe_polys, self.bad_polys, self.new_samples)
