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

    def __init__(self):
        self.plotdir = tempfile.mkdtemp(dir=PLOT_FILES_DIR)
        self.result_file = str(os.path.join(self.plotdir, "result.pdf"))
        self.result_tmp_file = str(os.path.join(self.plotdir, "result_tmp.pdf"))

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
        
    @abstractmethod
    def generate_constraints(self, samples_input, parameters, threshold, safe_above_threshold, threshold_area):
        raise NotImplementedError("Abstract parent method")