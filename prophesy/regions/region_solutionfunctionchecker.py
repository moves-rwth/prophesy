from prophesy.regions.region_smtchecker import SmtRegionChecker
import prophesy.adapter.pycarl as pc
from prophesy.adapter.pycarl import Constraint, Relation
from prophesy.smt.smt import VariableDomain
from prophesy.data.samples import ParameterInstantiation, InstantiationResult


class SolutionFunctionRegionChecker(SmtRegionChecker):
    """
    
    """

    def __init__(self, backend):
        """
        
        :param backend: 
        """
        super().__init__(backend)
        self._ratfunc = None

    def initialize(self, problem_description, threshold, constants=None):
        """
        Initializes the smt solver to consider the problem at hand.

        :param problem_description: 
        :type problem_description: ProblemDescription
        :param threshold: 
        :param constants: 
        """
        assert problem_description.solutionfunction is not None
        assert problem_description.parameters is not None
        self._ratfunc = problem_description.solutionfunction
        self.parameters = problem_description.parameters

        for p in self.parameters:
            self._smt2interface.add_variable(p.variable.name, VariableDomain.Real)

        safeVar = pc.Variable("__safe", pc.VariableType.BOOL)
        badVar = pc.Variable("__bad", pc.VariableType.BOOL)
        thresholdVar = pc.Variable("T")
        rf1Var = pc.Variable("rf1")
        rf2Var = pc.Variable("rf2")

        self._smt2interface.add_variable(safeVar, VariableDomain.Bool)
        self._smt2interface.add_variable(badVar, VariableDomain.Bool)
        self._smt2interface.add_variable(thresholdVar, VariableDomain.Real)


        if pc.denominator(self._ratfunc) != 1:
            self._smt2interface.add_variable(rf1Var, VariableDomain.Real)
            self._smt2interface.add_variable(rf2Var, VariableDomain.Real)
            safe_constraint = Constraint(pc.Polynomial(rf1Var) - thresholdVar * rf2Var, safe_relation)
            bad_constraint = Constraint(pc.Polynomial(rf1Var) - thresholdVar * rf2Var, bad_relation)
            rf1_constraint = Constraint(pc.Polynomial(rf1Var) - pc.numerator(result.ratfunc), Relation.EQ)
            rf2_constraint = Constraint(pc.Polynomial(rf2Var) - pc.denominator(result.ratfunc), Relation.EQ)
            self._smt2interface.assert_constraint(rf1_constraint)
            self._smt2interface.assert_constraint(rf2_constraint)
        else:
            safe_constraint = Constraint(pc.numerator(self._ratfunc) - thresholdVar, self._safe_relation)
            bad_constraint = Constraint(pc.numerator(self._ratfunc) - thresholdVar, self._bad_relation)

        threshold_constraint = Constraint(pc.Polynomial(thresholdVar) - threshold, Relation.EQ)

        self._smt2interface.assert_constraint(threshold_constraint)
        self._smt2interface.assert_guarded_constraint("__safe", safe_constraint)
        self._smt2interface.assert_guarded_constraint("__bad", bad_constraint)


    def _evaluate(self, smt_model):
        sample = ParameterInstantiation()
        for par in self.parameters:
            value = smt_model[par.variable.name]
            rational = pc.Rational(value)
            sample[par] = rational
        eval_dict = dict([(k.variable, v) for k, v in sample.items()])
        value = self._ratfunc.evaluate(eval_dict)
        return InstantiationResult(sample, value)