from prophesy.regions.region_checker import RegionChecker, RegionCheckResult
from prophesy.data.hyperrectangle import HyperRectangle

import time
from prophesy.smt.smt import Answer
from prophesy.data.samples import SamplePoint, Sample
from pycarl import Rational
from prophesy.data.constraint import region_from_hyperrectangle,\
    region_from_polygon

class SmtRegionChecker(RegionChecker):
    def __init__(self, smt2interface, parameters, ratfunc):
        """
        @param smt2interface SMTSolver to check regions with
        @param parameters ParameterOrder
        @param ratfunc RationalFunction, used to evaluate solutions
        """
        self._smt2interface = smt2interface
        self.parameters = parameters
        self._ratfunc = ratfunc

        self.benchmark_output = []

    def print_info(self):
        i = 1
        print("no.  result   time  tot. time   area  tot. area")
        total_sec = 0
        total_area = 0
        for benchmark in self.benchmark_output:
            total_sec = total_sec + benchmark[1]
            if benchmark[0] == Answer.unsat:
                total_area = total_area + benchmark[2]
            print("{:3}   {:>6s}  {:5.2f}     {:6.2f}  {:4.3f}      {:4.3f}".format(i, benchmark[0].name, benchmark[1], total_sec, float(benchmark[2]), float(total_area)))
            i = i + 1

    def analyse_region(self, polygon, safe):
        """Extends the current area by using the new polygon
        regions are the newly added regions for the polygon
        polygon marks the new area to cover
        safe indicates whether the area is safe or bad
        returns tuple (valid constraint, polygon/counterexample point)
        if constraint is valid the tuple  is (True, polygon added)
        if constraint is invalid the tuple is (False, point as counterexample)
        @param polygon, either HyperRectangle or shapely Polygon
        @param safe Boolean to indicate if the region should be considered as
            safe or unsafe
        """
        smt_successful = False
        smt_model = None

        variables = self.parameters.get_variable_order()
        if isinstance(polygon, HyperRectangle):
            constraint = region_from_hyperrectangle(polygon, variables)
        else:
            constraint = region_from_polygon(polygon, variables)

        while not smt_successful:
            # check constraint with smt
            with self._smt2interface as smt_context:
                smt_context.assert_constraint(constraint)

                # Invert the safe flag to try and find a counter example
                smt_context.set_guard("__safe", not safe)
                smt_context.set_guard("__bad", safe)

                start = time.time()
                checkresult = smt_context.check()
                duration = time.time() - start
                #print("Call took {0} seconds".format(duration))
                if isinstance(polygon, HyperRectangle):
                    self.benchmark_output.append((checkresult, duration, polygon.size()))
                else:
                    self.benchmark_output.append((checkresult, duration, polygon.area))
                #self.print_benchmark_output(self.benchmark_output)
                if not checkresult in [Answer.sat, Answer.unsat]:
                    # smt call not finished -> change constraint to make it better computable
                    # TODO what to do in GUI?
                    #print("{}: Change constraint for better computation".format(checkresult))
                    break
                else:
                    smt_successful = True
                    if checkresult == Answer.sat:
                        smt_model = smt_context.get_model()
                    break

        if checkresult == Answer.unsat:
            return RegionCheckResult.unsat, None
        elif checkresult == Answer.sat:
            # add new point as counter example to existing regions
            sample = SamplePoint()
            for var in variables:
                value = smt_model[var.name]
                rational = Rational(value)
                sample[var] = rational
            value = self._ratfunc.eval(sample)
            return RegionCheckResult.sat, Sample.from_sample_point(sample, variables, value)
        else:
            # SMT failed completely
            return RegionCheckResult.unknown, None
