import time

from prophesy.regions.region_checker import RegionChecker, RegionCheckResult
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.smt.smt import Answer, VariableDomain
from prophesy.data.samples import ParameterInstantiation, InstantiationResult
from prophesy.adapter.pycarl import Rational
from prophesy.data.constraint import region_from_polygon


import prophesy.adapter.pycarl as pc
from prophesy.data.interval import Interval, BoundType
from prophesy.adapter.pycarl import Constraint, Relation



class SmtRegionChecker(RegionChecker):
    def __init__(self, smt2interface, parameters, ratfunc):
        """
        :param smt2interface: SMTSolver to check regions with
        :param parameters: ParameterOrder
        :param ratfunc: RationalFunction, used to evaluate solutions
        """
        self._smt2interface = smt2interface
        self.parameters = parameters
        self._ratfunc = ratfunc

        self.benchmark_output = []

    # Can we set the lower rat_func_bound to an open interval, thus exclude the zero?
    def initialize(self, result, threshold,
                                        solution_bound=Interval(0, BoundType.closed, None, BoundType.open)):
        """
        Initializes the smt solver to consider the problem at hand.
        
        :param result: 
        :param threshold: 
        :param solution_bound: 
        """
        for p in result.parameters:
            self._smt2interface.add_variable(p.variable.name, VariableDomain.Real)

        safeVar = pc.Variable("__safe", pc.VariableType.BOOL)
        badVar = pc.Variable("__bad", pc.VariableType.BOOL)
        thresholdVar = pc.Variable("T")
        rf1Var = pc.Variable("rf1")
        rf2Var = pc.Variable("rf2")

        self._smt2interface.add_variable(safeVar, VariableDomain.Bool)
        self._smt2interface.add_variable(badVar, VariableDomain.Bool)
        self._smt2interface.add_variable(thresholdVar, VariableDomain.Real)

        safe_relation = pc.Relation.GEQ
        bad_relation = pc.Relation.LESS

        if pc.denominator(result.ratfunc) != 1:
            self._smt2interface.add_variable(rf1Var, VariableDomain.Real)
            self._smt2interface.add_variable(rf2Var, VariableDomain.Real)
            safe_constraint = Constraint(pc.Polynomial(rf1Var) - thresholdVar * rf2Var, safe_relation)
            bad_constraint = Constraint(pc.Polynomial(rf1Var) - thresholdVar * rf2Var, bad_relation)
            rf1_constraint = Constraint(rf1Var - pc.numerator(result.ratfunc), Relation.EQ)
            rf2_constraint = Constraint(rf2Var - pc.denominator(result.ratfunc), Relation.EQ)
            self._smt2interface.assert_constraint(rf1_constraint)
            self._smt2interface.assert_constraint(rf2_constraint)
        else:
            safe_constraint = Constraint(pc.numerator(result.ratfunc) - thresholdVar, safe_relation)
            bad_constraint = Constraint(pc.numerator(result.ratfunc) - thresholdVar, bad_relation)

        threshold_constraint = Constraint(pc.Polynomial(thresholdVar) - threshold, Relation.EQ)

        self._smt2interface.assert_constraint(threshold_constraint)
        self._smt2interface.assert_guarded_constraint("__safe", safe_constraint)
        self._smt2interface.assert_guarded_constraint("__bad", bad_constraint)

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
                #self.print_benchmark_output(self.benchmark_output)
                if not checkresult in [Answer.sat, Answer.unsat]:
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
            eval_dict = dict([(k.variable, v) for k,v in sample.items()])
            value = self._ratfunc.evaluate(eval_dict)
            return RegionCheckResult.CounterExample, InstantiationResult(sample, value)
        else:
            # SMT failed completely
            return RegionCheckResult.unknown, None
