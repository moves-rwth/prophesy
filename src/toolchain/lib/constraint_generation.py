import tempfile
import time
import os
import sampling
import smt.smt
from output.plot import Plot
from abc import ABCMeta, abstractmethod
#needed for pdf merging for debugging
from subprocess import call
from config import PLOT_FILES_DIR, EPS
from util import ensure_dir_exists
from data.constraint import Constraint
from sympy.polys.polytools import Poly
import shutil
from shapely.geometry import Point, asPoint

class ConstraintGeneration(object):
    __metaclass__ = ABCMeta

    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc):
        if len(parameters) != 2:
            raise NotImplementedError

        self.plotdir = PLOT_FILES_DIR
        ensure_dir_exists(self.plotdir)
        (_, self.result_file) = tempfile.mkstemp(suffix=".pdf", prefix="result_", dir=self.plotdir)
        self.first_pdf = True
        self.samples = samples.copy()
        self.safe_samples = None
        self.bad_samples = None
        self.parameters = parameters
        self.threshold = threshold
        self.safe_above_threshold = safe_above_threshold
        self.threshold_area = threshold_area

        self.smt2interface = _smt2interface
        self.ratfunc = _ratfunc
        self.nr = 0
        self.benchmark_output = []
        # Stores all constraints as triple ([constraint], polygon representation, bad/safe)
        self.all_constraints = []

         # initial constraints
        self.smt2interface.push()
        for param in self.parameters:
            # add constraints 0 <= param <= 1
            self.smt2interface.assert_constraint(Constraint(Poly(param, self.parameters), ">=", self.parameters))
            self.smt2interface.assert_constraint(Constraint(Poly(param - 1, self.parameters), "<=", self.parameters))

    def add_pdf(self, name):
        """Adds pdf with name to result.pdf in tmp directory
        first indicates if resultfile exists already"""
        if self.first_pdf:
            self.first_pdf = False
            shutil.copyfile(name, self.result_file)
        else:
            (_, result_tmp_file) = tempfile.mkstemp(".pdf", dir=self.plotdir)
            call(["pdfunite", self.result_file, name, result_tmp_file])
            try:
                shutil.move(result_tmp_file, self.result_file)
            except:
                os.unlink(result_tmp_file)

    def compute_constraints(self, polygon):
        """Compute constraints from polygon
        returns list of constraints describing the polygon
        """
        assert(len(list(polygon.interiors)) == 0)
        new_constraints = []
        poly_points = list(polygon.exterior.coords)
        for i in range(0, len(poly_points)-1):
            point1 = Point(poly_points[i])
            point2 = Point(poly_points[i+1])

            if (abs(point1.x - point2.x) < EPS):
                # vertical line
                if (point1.y < point2.y):
                    rel = "<"
                else:
                    rel = ">="
                new_constraints.append(Constraint(Poly(self.parameters[0] - point1.x, self.parameters), rel, self.parameters))
                #print("line is described by x = {0}".format(point1.x))
            else:
                # asserted x2 != x1
                # slope
                m = (point2.y - point1.y) / (point2.x - point1.x)
                # two-point form
                #     y-y1 = m * (x-x1)
                # <=> 0 = mx - mx1 - y + y1
                # <=> 0 = mx - y + c with c = y1 - mx1
                c = point1.y - m * point1.x

                # As we go counterclockwise, the described area is always left of the line
                rel = ">"

                new_constraints.append(Constraint(Poly(m*self.parameters[0] - self.parameters[1] + c, self.parameters), rel, self.parameters))
                #print("line is described by {m}x - y + {c} = 0".format(m=m, c=c))

        print("Constraints for polygon ({0}): {1}".format(polygon, new_constraints))
        return new_constraints

    @classmethod
    def is_point_fulfilling_constraint(cls, pt, constraint):
        """Check wether the given point is satisfied by the constraints
        (i.e. is contained by it)"""
        pol = constraint.polynomial
        parameters = constraint.symbols
        evaluation = sampling.get_evaluation(pt, parameters)

        pol = pol.subs(evaluation).evalf(EPS)

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
            total_sec  =  total_sec + benchmark[1]
            if benchmark[0] == smt.smt.Answer.unsat:
                total_area =  total_area + benchmark[2]
            print("{:3}".format(i) + "   {:>5s}".format(benchmark[0].name) + "  {:5.2f}".format(benchmark[1]) + "     {:6.2f}".format(total_sec) + "  {:4.3f}".format(benchmark[2]) + "      {:4.3f}".format(total_area))
            i = i + 1

    def plot_results(self, anchor_points = [], additional_arrows = [], additional_lines_green = [], additional_lines_red = [], additional_lines_blue = [], additional_boxes_green = [], additional_boxes_red = [], additional_boxes_blue = [], additional_polygons_green = [], additional_polygons_red = [], additional_polygons_blue = [], display=False, first=False):
        # plot result
        (_, result_tmp_file) = tempfile.mkstemp(".pdf", dir=self.plotdir)
        Plot.plot_results(self.parameters, dict([(p, v > self.threshold) for p,v in self.samples.items()]), anchor_points, additional_arrows, additional_lines_green, additional_lines_red, additional_lines_blue, additional_boxes_green, additional_boxes_red, additional_boxes_blue, additional_polygons_green, additional_polygons_red, additional_polygons_blue, result_tmp_file, display)
        self.add_pdf(result_tmp_file)
        os.unlink(result_tmp_file)

    @abstractmethod
    def next_constraint(self):
        """Generate a new set of constraints ([constraints], area, area_safe),
        where [constraints] is a list of Constraint, area is a polygon representation of the new area
        and area_safe indicated whether the area should be determined safe (or not)"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def change_current_constraint(self):
        """Update current set of constraints (see next_constraint), usually to avoid mem or time out"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def finalize_step(self, new_constraints):
        """Final steps to execute after last call of next_constraint, usually plots things"""
        raise NotImplementedError("Abstract parent method")

    def analyze_constraint(self, constraints, polygon, safe):
        """Extends the current area by using the new polygon
        constraints are the newly added constraints for the polygon
        polygon marks the new area to cover
        safe indicates whether the area is safe or bad
        returns tuple (valid constraint, polygon/counterexample point)
        if constraint is valid the tuple  is (True, polygon added)
        if constraint is invalid the tuple is (False, point as counterexample)
        """
        assert(polygon is not None)
        self.nr += 1
        smt_successful = False
        smt_model = None
        result = None

        while not smt_successful:
            # check constraint with smt
            with self.smt2interface as smt_context:
                for constraint in constraints:
                    smt_context.assert_constraint(constraint)

                smt_context.set_guard("safe", not safe)
                smt_context.set_guard("bad", safe)
                print("Calling smt solver")
                start = time.time()
                checkresult = smt_context.check()
                duration = time.time() - start
                print("Call took {0} seconds".format(duration))
                self.benchmark_output.append((checkresult, duration, polygon.area))
                if checkresult == smt.smt.Answer.killed or checkresult == smt.smt.Answer.memout:
                    # smt call not finished -> change constraint to make it better computable
                    #TODO what to do in GUI?
                    result_update = self.change_current_constraint()
                    if result_update == None:
                        break
                    (constraints, area, safe) = result_update
                else:
                    smt_successful = True
                    if checkresult == smt.smt.Answer.sat:
                        smt_model = smt_context.get_model()
                    break

        if checkresult == smt.smt.Answer.unsat:
            # update list of all constraints
            self.all_constraints.append((constraints, polygon, safe))

            # remove unnecessary samples which are covered already by constraints
            for pt in list(self.samples.keys()):
                fullfillsAllConstraints = all([self.is_point_fulfilling_constraint(pt, constraint) for constraint in constraints])
                #TODO: Why delete, what if threshold changes?
                if fullfillsAllConstraints:
                    del self.samples[pt]

            # update everything in the algorithm according to correct new area
            #TODO what to do in GUI?
            self.finalize_step(constraints)
            print("added new polygon {0} with constraints: {1}".format(polygon, constraints))
            result = (True, polygon)

        elif checkresult == smt.smt.Answer.sat:
            # add new point as counter example to existing constraints
            modelPoint_tmp = ()
            for p in self.parameters:
                if p.name in smt_model:
                    modelPoint_tmp = modelPoint_tmp + (smt_model[p.name],)
                else:
                    # if parameter is undefined set as 0.5
                    modelPoint_tmp = modelPoint_tmp + (0.5,)
                    smt_model[p.name] = 0.5
            modelPoint = Point(modelPoint_tmp)
            self.samples[modelPoint] = self.ratfunc.subs(smt_model.items()).evalf()
            print("added new sample {0} with value {1}".format(modelPoint, self.samples[modelPoint]))
            result = (False, modelPoint)
        else:
            assert(false)

        self.print_benchmark_output(self.benchmark_output)
        return result

    def generate_constraints(self):
        """Iteratively generates new constraints, heuristically, attempting to
        find the largest safe or unsafe area"""
        while True:
            self.nr += 1

            # split samples into safe and bad
            (self.safe_samples, self.bad_samples) = sampling.split_samples(self.samples, self.threshold, self.safe_above_threshold)
            assert(len(self.safe_samples) + len(self.bad_samples) == len(self.samples))

            # get next constraint depending on algorithm
            result_constraint = self.next_constraint()
            if (result_constraint is None):
                # no new constraint available
                break

            (new_constraints, polygon, area_safe) = result_constraint
            self.analyze_constraint(new_constraints, polygon, area_safe)

        self.smt2interface.pop()
        self.smt2interface.stop()
        self.smt2interface.print_calls()

        print("Generation complete, plot located at {0}".format(self.result_file))