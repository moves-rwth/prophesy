from config import *
import sampling
from data.constraint import *
import smt.smt
from output.plot import Plot

import tempfile
import time
from abc import ABCMeta, abstractmethod

#needed for pdf merging for debugging
from subprocess import call

class ConstraintGeneration(object):
    __metaclass__ = ABCMeta

    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc):
        if len(parameters) != 2:
            raise NotImplementedError

        self.plotdir = tempfile.mkdtemp(dir=PLOT_FILES_DIR)
        self.result_file = str(os.path.join(self.plotdir, "result.pdf"))
        self.result_tmp_file = str(os.path.join(self.plotdir, "result_tmp.pdf"))
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
        self.all_constraints = []

    def add_pdf(self, name, first):
        # Adds pdf with name to result.pdf in tmp directory
        # first indicates if resultfile exists already
        if first:
            call(["cp", str(os.path.join(self.plotdir, "{0}.pdf".format(name))), self.result_file])
        else:
            call(["pdfunite", self.result_file, str(os.path.join(self.plotdir, "{0}.pdf".format(name))), self.result_tmp_file])
            call(["mv", self.result_tmp_file, self.result_file])

    @classmethod
    def is_point_fulfilling_constraint(cls, pt, parameters, constraint):
        pol = constraint.polynomial
        evaluation = zip(parameters, pt)

        for [variable, value] in evaluation:
            pol = pol.subs(variable, value).evalf(EPS)

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

    def plot_results(self, anchor_points = [], additional_arrows = [], additional_lines_green = [], additional_lines_red = [], additional_lines_blue = [], additional_boxes_green = [], additional_boxes_red = [], additional_boxes_blue = [], name="tmp", display=False, first=False):
        # plot result
        Plot.plot_results(self.parameters, dict([(p, v > self.threshold) for p,v in self.samples.items()]), anchor_points, additional_arrows, additional_lines_green, additional_lines_red, additional_lines_blue, additional_boxes_green, additional_boxes_red, additional_boxes_blue, os.path.join(self.plotdir, "{0}.pdf".format(name)), display)
        self.add_pdf(name, first)

    @abstractmethod
    def next_constraint(self):
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def change_current_constraint(self):
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def finalize_step(self, new_constraints):
        raise NotImplementedError("Abstract parent method")

    def generate_constraints(self):
        constraint_available = True
        benchmark_output = []

        while constraint_available:
            self.nr += 1

            # split samples into safe and bad
            (self.safe_samples, self.bad_samples) = sampling.split_samples(self.samples, self.threshold, self.safe_above_threshold)
            assert(len(self.safe_samples) + len(self.bad_samples) == len(self.samples))

            # get next constraint depending on algorithm
            result_constraint = self.next_constraint()
            if (result_constraint is None):
                # no new constraint available
                constraint_available = False
                break

            (new_constraints, area, area_safe) = result_constraint

            smt_successful = False
            while not smt_successful:
                # check constraint with smt
                self.smt2interface.push()
                for constraint in new_constraints:
                    self.smt2interface.assert_constraint(constraint)

                self.smt2interface.set_guard("safe", not area_safe)
                self.smt2interface.set_guard("bad", area_safe)
                print("Calling smt solver")
                start = time.time()
                checkresult = self.smt2interface.check()
                duration = time.time() - start
                print("Call took {0} seconds".format(duration))
                benchmark_output.append((checkresult, duration, area))
                if checkresult == smt.smt.Answer.killed or checkresult == smt.smt.Answer.memout:
                    self.smt2interface.pop()
                    # smt call not finished -> change constraint to make it better computable
                    (new_constraints, area) = self.change_current_constraint()
                else:
                    smt_successful = True
                    break

            # update list of all constraints
            self.all_constraints.append(new_constraints)

            if checkresult == smt.smt.Answer.unsat:
                # remove unnecessary samples which are covered already by constraints
                for pt, v in list(self.samples.items()):
                    fullfillsAllConstraints = True
                    for constraint in new_constraints:
                        if not self.is_point_fulfilling_constraint(pt, self.parameters, constraint):
                            fullfillsAllConstraints = False
                            break;
                    if fullfillsAllConstraints:
                        del self.samples[pt]

                # update everything in the algorithm according to correct new area
                self.finalize_step(new_constraints)

            elif checkresult == smt.smt.Answer.sat:
                model = self.smt2interface.get_model()
                # add new point as counter example to existing constraints
                modelPoint = ()
                for p in self.parameters:
                    if p.name in model:
                        modelPoint = modelPoint + (model[p.name],)
                    else:
                        # if parameter is undefined set as 0.5
                        modelPoint = modelPoint + (0.5,)
                        model[p.name] = 0.5

                self.samples[modelPoint] = self.ratfunc.evaluate(model.items())
                print("added new sample {0} with value {1}".format(modelPoint, self.samples[modelPoint]))

            self.smt2interface.pop()
            self.print_benchmark_output(benchmark_output)

        self.smt2interface.stop()
        self.smt2interface.print_calls()

        return