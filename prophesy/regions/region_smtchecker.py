import time

from prophesy.regions.region_checker import RegionChecker, RegionCheckResult
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.smt.smt import Answer, VariableDomain
from prophesy.data.samples import ParameterInstantiation, InstantiationResult
from prophesy.adapter.pycarl import Rational
from prophesy.data.constraint import region_from_polygon
from abc import abstractmethod


class SmtRegionChecker(RegionChecker):
    def __init__(self, backend):
        """
        :param backend: Smt solver to check regions
        :type backend: SMTSolver
        :param parameters: The parameters of the problem
        :type parameters: ParameterOrder
        """
        self._smt2interface = backend
        self.parameters = None
        self._ratfunc = None
        self.benchmark_output = []

    @abstractmethod
    def initialize(self, problem_description, threshold, constants=None):
        raise NotImplementedError("Calling an abstract method")

    def print_info(self):
        i = 1
        print("no.  result   time  tot. time   area  tot. area")
        total_sec = 0
        total_area = 0
        for benchmark in self.benchmark_output:
            total_sec = total_sec + benchmark[1]
            if benchmark[0] == Answer.unsat:
                total_area = total_area + benchmark[2]
            print("{:3}   {:>6s}  {:5.2f}     {:6.2f}  {:4.3f}      {:4.3f}".format(i, benchmark[0].name, benchmark[1],
                                                                                    total_sec, float(benchmark[2]),
                                                                                    float(total_area)))
            i = i + 1

    def analyse_region(self, polygon, safe):
        """
        Extends the current area by using the new polygon
        regions are the newly added regions for the polygon
        polygon marks the new area to cover
        safe indicates whether the area is safe or bad
        returns tuple (valid constraint, polygon/counterexample point)
        if constraint is valid the tuple  is (True, polygon added)
        if constraint is invalid the tuple is (False, point as counterexample)
        
        :param polygon: either HyperRectangle or shapely Polygon
        :param safe: Boolean to indicate if the region should be considered as safe or unsafe
        """
        smt_successful = False
        smt_model = None

        variables = self.parameters.get_variables()
        if isinstance(polygon, HyperRectangle):
            constraint = polygon.to_formula(variables)
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
                if isinstance(polygon, HyperRectangle):
                    self.benchmark_output.append((checkresult, duration, polygon.size()))
                else:
                    self.benchmark_output.append((checkresult, duration, polygon.area))
                if checkresult not in [Answer.sat, Answer.unsat]:
                    break
                else:
                    if checkresult == Answer.sat:
                        smt_model = smt_context.get_model()
                    break

        if checkresult == Answer.unsat:
            return RegionCheckResult.Satisfied, None
        elif checkresult == Answer.sat:
            # add new point as counter example to existing regions
            sample = ParameterInstantiation()
            for par in self.parameters:
                value = smt_model[par.variable.name]
                rational = Rational(value)
                sample[par] = rational
            eval_dict = dict([(k.variable, v) for k, v in sample.items()])
            value = self._ratfunc.evaluate(eval_dict)
            return RegionCheckResult.CounterExample, InstantiationResult(sample, value)
        else:
            # SMT failed completely
            return RegionCheckResult.unknown, None
