import os
import shutil
import tempfile
import time
from abc import ABCMeta, abstractmethod
from enum import Enum

from numpy import array
from shapely.geometry.polygon import Polygon, orient, LinearRing
from sympy.polys.polytools import Poly

# needed for pdf merging for debugging
import config

import smt.smt
from data.constraint import Constraint, ComplexConstraint
from output.plot import Plot
from util import ensure_dir_exists
from config import configuration
from exceptions.module_error import ModuleError

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
        vector = {Direction.NE: array([ 1,  1]),
                  Direction.SE: array([ 1, -1]),
                  Direction.NW: array([-1,  1]),
                  Direction.SW: array([-1, -1])}
        return vector[self]


class Anchor:
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


class ConstraintGeneration:
    """A generator for regions. This class acts as an iterable that
    generates new regions (or counterexamples) until the search space is exhausted
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
        # Stores all regions as triple ([constraint], polygon representation, bad/safe)
        self.all_constraints = []
        self.safe_polys = []
        self.bad_polys = []
        self.new_samples = {}

        self.plot = True
        self.first_pdf = True
        ensure_dir_exists(config.PLOTS)
        _, self.result_file = tempfile.mkstemp(suffix=".pdf", prefix="result_", dir=config.PLOTS)

    def __iter__(self):
        # Prime the generator
        return next(self)

    def __next__(self):
        with self.smt2interface as smtcontext:
            # initial regions
            for param in self._symbols():
                #TODO fix assumption that param is between zero and 1
                # add regions 0 <= param <= 1
                smtcontext.assert_constraint(Constraint(Poly(param, self._symbols()), ">=", self._symbols()))
                smtcontext.assert_constraint(Constraint(Poly(param - 1, self._symbols()), "<=", self._symbols()))

            # get next constraint depending on algorithm
            result_constraint = self.next_constraint()
            while result_constraint is not None:
                new_constraint, polygon, area_safe = result_constraint
                result = self.analyze_constraint(new_constraint, polygon, area_safe)
                if result is None:
                    # End of generator
                    return
                yield result

                # get next constraint depending on algorithm
                result_constraint = self.next_constraint()
        # End of generator
        return

    def _symbols(self):
        return list([x[0] for x in self.parameters])

    def _intervals(self):
        return list([x[1] for x in self.parameters])

    def _add_pdf(self, name):
        """
        Adds pdf with name to result.pdf in tmp directory
        """
        #TODO Only do this if the option is installed.
        if not configuration.is_module_available("pypdf2"):
            raise ModuleError("Module pypdf2 is needed for using the pdf export for regions. Maybe your config is oudated?")
        from PyPDF2 import PdfFileMerger, PdfFileReader

        if self.first_pdf:
            self.first_pdf = False
            shutil.copyfile(name, self.result_file)
            print("Plot file located at {0}".format(self.result_file))
        else:
            merger = PdfFileMerger()
            merger.append(PdfFileReader(self.result_file, 'rb'))
            merger.append(PdfFileReader(name, 'rb'))
            merger.write(self.result_file)

    def compute_constraint(self, polygon):
        """Compute regions from polygon (Polygon, LineString or LinearRing)
        Area will be considered at the rhs (ccw) of line segments
        :param polygon: must be convex
        :return: single (Complex)Constraint describing the polygon
        """
        if isinstance(polygon, LinearRing):
            # Convert to polygon so it can be oriented
            polygon = Polygon(polygon)

        if isinstance(polygon, Polygon):
            assert len(list(polygon.interiors)) == 0
            polygon = orient(polygon, sign=1.0)
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
            poly = Poly(-c, self._symbols())
            for parameter, coefficient in zip(self._symbols(), dvec):
                if coefficient != 0:
                    poly = Poly(poly + parameter * coefficient, self._symbols())

            # TODO: '<=' as polygon is CCW oriented, not sure if this applies to n-dimen
            new_constraint = Constraint(poly, "<=", self._symbols())
            if constraint is None:
                constraint = new_constraint
            else:
                constraint = constraint & new_constraint

        # print("constraint: {0}".format(constraint))
        return constraint

    @classmethod
    def is_point_fulfilling_constraint(cls, pt, constraint):
        """Check whether the given point is satisfied by the regions
        (i.e. is contained by it)"""
        if isinstance(constraint, ComplexConstraint):
            if constraint.operator == "or":
                return any([cls.is_point_fulfilling_constraint(pt, sub_constraint) for sub_constraint in constraint.constraints])
            elif constraint.operator == "and":
                return all([cls.is_point_fulfilling_constraint(pt, sub_constraint) for sub_constraint in constraint.constraints])
            else:
                assert False, "Unknown constraint operator {}".format(constraint.operator)

        pol = constraint.polynomial.eval({x: y for x, y in zip(constraint.symbols, pt)}).evalf()

        if constraint.relation == "=":
            return abs(pol) < config.PRECISION
        elif constraint.relation == "<":
            return pol < 0
        elif constraint.relation == ">":
            return pol > 0
        elif constraint.relation == "<=":
            return pol <= 0
        elif constraint.relation == ">=":
            return pol >= 0
        elif constraint.relation == "<>":
            return abs(pol) > config.PRECISION

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
            print("{:3}   {:>6s}  {:5.2f}     {:6.2f}  {:4.3f}      {:4.3f}".format(i, benchmark[0].name, benchmark[1], total_sec, benchmark[2], total_area))
            i = i + 1

    def plot_candidate(self):
        pass

    def plot_results(self, *args, **kwargs):
        if not self.plot:
            return
        # Extend arguments
        poly_green = kwargs.get('poly_green')
        if poly_green is None:
            poly_green = []
        kwargs['poly_green'] = poly_green + self.safe_polys
        poly_red = kwargs.get('poly_red')
        if poly_red is None:
            poly_red = []
        kwargs['poly_red'] = poly_red + self.bad_polys

        # Split samples appropriately
        samples_green = [pt for pt, v in self.samples.items() if v >= self.threshold]
        samples_red = [pt for pt, v in self.samples.items() if v < self.threshold]

        _, result_tmp_file = tempfile.mkstemp(".pdf", dir=config.PLOTS)
        Plot.plot_results(parameters=self.parameters,
                          samples_green=samples_green,
                          samples_red=samples_red,
                          path_to_save=result_tmp_file,
                          *args, **kwargs)
        self._add_pdf(result_tmp_file)
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
        """Generate a new set of regions ([regions], area, area_safe),
        where [regions] is a list of Constraint, area is a polygon representation of the new area
        and area_safe indicated whether the area should be determined safe (or not)"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def fail_constraint(self, constraint, safe):
        """Update current set of regions, usually to avoid mem or time out.
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
        regions are the newly added regions for the polygon
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
                    if result_update is None:
                        break
                    self.plot_candidate()
                    constraint, polygon, safe = result_update
                else:
                    smt_successful = True
                    if checkresult == smt.smt.Answer.sat:
                        smt_model = smt_context.get_model()
                    break

        if checkresult == smt.smt.Answer.unsat:
            # remove unnecessary samples which are covered already by regions
            for pt in list(self.samples.keys()):
                if self.is_point_fulfilling_constraint(pt, constraint):
                    del self.samples[pt]

            # update everything in the algorithm according to correct new area
            self.accept_constraint(constraint, safe)
            return True, (constraint, polygon, safe)
        elif checkresult == smt.smt.Answer.sat:
            # add new point as counter example to existing regions
            model_point = ()
            for p in self._symbols():
                if p.name in smt_model:
                    model_point = model_point + (smt_model[p.name],)
                else:
                    # if parameter is undefined set as 0.5
                    model_point = model_point + (0.5,)
                    smt_model[p.name] = 0.5
            value = self.ratfunc.subs(smt_model.items()).evalf()
            self.reject_constraint(constraint, safe, (model_point, value))
            return False, (model_point, value)
        else:
            # SMT failed completely
            return None

    def generate_constraints(self, max_iter=-1, max_area=1.0):
        """Iteratively generates new regions, heuristically, attempting to
        find the largest safe or unsafe area
        max_iter: Number of regions to generate/check at most (not counting SMT failures),
        -1 for unbounded"""
        if max_iter == 0:
            return self.safe_polys, self.bad_polys, self.new_samples

        for result in self:
            unsat, data = result
            if unsat:
                self.all_constraints.append(data)
                constraint, poly, safe = data
                if safe:
                    self.safe_polys.append(poly)
                else:
                    self.bad_polys.append(poly)
                print("added new polygon {0} with constraint: {1}".format(poly, constraint))
            else:
                point, value = data
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
                self.plot_results(display=False)

        # Plot the final outcome
        if self.plot:
            self.plot_results(display=False)
            print("Generation complete, plot located at {0}".format(self.result_file))
        self.print_benchmark_output(self.benchmark_output)

        return self.safe_polys, self.bad_polys, self.new_samples
