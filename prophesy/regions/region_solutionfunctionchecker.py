from prophesy.regions.region_smtchecker import SmtRegionChecker
import prophesy.adapter.pycarl as pc
from prophesy.adapter.pycarl import Constraint, Relation
from prophesy.smt.smt import VariableDomain
from prophesy.data.samples import ParameterInstantiation, InstantiationResult
from prophesy.data.property import OperatorType
import logging

logger = logging.getLogger(__name__)


class SolutionFunctionRegionChecker(SmtRegionChecker):
    """
    
    """

    def __init__(self, backend):
        """
        
        :param backend: 
        """
        super().__init__(backend)
        self._ratfunc = None
        self.fixed_threshold = True
        self._thresholdVar = None

    def initialize(self, problem_description, constants=None, fixed_threshold = True):
        """
        Initializes the smt solver to consider the problem at hand.

        :param problem_description: 
        :type problem_description: ProblemDescription
        :param threshold: 
        :param constants: 
        """

        self.fixed_threshold = fixed_threshold
        lower_bounded_variables = True
        upper_bounded_variables = False
        assert problem_description.solutionfunction is not None
        assert problem_description.parameters is not None
        if self.fixed_threshold:
            assert problem_description.threshold is not None
        self._ratfunc = problem_description.solutionfunction
        self.parameters = problem_description.parameters

        for p in self.parameters:
            self._smt2interface.add_variable(p.variable.name, VariableDomain.Real)

        safeVar = pc.Variable("__safe", pc.VariableType.BOOL)
        badVar = pc.Variable("__bad", pc.VariableType.BOOL)
        self._thresholdVar = pc.Variable("T")
        rf1Var = pc.Variable("rf1")
        rf2Var = pc.Variable("rf2")

        self._smt2interface.add_variable(safeVar, VariableDomain.Bool)
        self._smt2interface.add_variable(badVar, VariableDomain.Bool)
        self._smt2interface.add_variable(self._thresholdVar, VariableDomain.Real)

        if pc.denominator(self._ratfunc) != 1:
            for constraint in problem_description.welldefined_constraints:
                if not constraint.lhs.total_degree <= 1 or constraint.relation == pc.Relation.NEQ:
                    raise RuntimeError("Non-linear well-definednessconstraints are not supported right now")
            # We do know now that the well-defined points are connected.
            sample = self._get_welldefined_point(problem_description.welldefined_constraints)
            eval_dict = dict([(k.variable, v) for k, v in sample.items()])
            value = pc.denominator(self._ratfunc).evaluate(eval_dict)
            self._smt2interface.add_variable(rf1Var, VariableDomain.Real)
            self._smt2interface.add_variable(rf2Var, VariableDomain.Real)
            if upper_bounded_variables and problem_description.property.operator == OperatorType.probability:
                self._smt2interface.assert_constraint(pc.Constraint(pc.Polynomial(rf1Var) - rf2Var, pc.Relation.LESS))
            if value < 0:
                if lower_bounded_variables:
                    self._smt2interface.assert_constraint(pc.Constraint(rf1Var, pc.Relation.LESS, pc.Rational(0)))
                    self._smt2interface.assert_constraint(pc.Constraint(rf2Var, pc.Relation.LESS, pc.Rational(0)))

                safe_constraint = Constraint(pc.Polynomial(rf1Var) - self._thresholdVar * rf2Var, self._bad_relation)
                bad_constraint = Constraint(pc.Polynomial(rf1Var) - self._thresholdVar * rf2Var, self._safe_relation)
            else:
                if bounded_variables:
                    self._smt2interface.assert_constraint(pc.Constraint(rf1Var, pc.Relation.GREATER, pc.Rational(0)))
                    self._smt2interface.assert_constraint(pc.Constraint(rf2Var, pc.Relation.GREATER, pc.Rational(0)))

                safe_constraint = Constraint(pc.Polynomial(rf1Var) - self._thresholdVar * rf2Var, self._safe_relation)
                bad_constraint = Constraint(pc.Polynomial(rf1Var) - self._thresholdVar * rf2Var, self._bad_relation)
            rf1_constraint = Constraint(pc.Polynomial(rf1Var) - pc.numerator(self._ratfunc), Relation.EQ)
            rf2_constraint = Constraint(pc.Polynomial(rf2Var) - pc.denominator(self._ratfunc), Relation.EQ)
            self._smt2interface.assert_constraint(rf1_constraint)
            self._smt2interface.assert_constraint(rf2_constraint)
        else:
            safe_constraint = Constraint(pc.numerator(self._ratfunc) - self._thresholdVar, self._safe_relation)
            bad_constraint = Constraint(pc.numerator(self._ratfunc) - self._thresholdVar, self._bad_relation)

        self._smt2interface.assert_guarded_constraint("__safe", safe_constraint)
        self._smt2interface.assert_guarded_constraint("__bad", bad_constraint)
        if self.fixed_threshold:
            self._add_threshold_constraint(problem_description.threshold)

    def change_threshold(self, new_threshold):
        assert self.fixed_threshold is not True
        #TODO check that the interface is at the level where we pushed the threshold.
        self._smt2interface.pop()
        self._smt2interface.push()
        self._add_threshold_constraint(new_threshold)

    def _add_threshold_constraint(self, threshold):
        threshold_constraint = pc.Constraint(pc.Polynomial(self._thresholdVar) - threshold,
                                             pc.Relation.EQ)
        self._smt2interface.assert_constraint(threshold_constraint)


    def _get_welldefined_point(self, constraints):
        extrasmt2 = type(self._smt2interface)()
        extrasmt2.run()
        for p in self.parameters:
            extrasmt2.add_variable(p.variable.name, VariableDomain.Real)
        for constraint in constraints:
            extrasmt2.assert_constraint(constraint)
        extrasmt2.check()
        smt_model = extrasmt2.get_model()
        result = self._smt_model_to_sample(smt_model)
        extrasmt2.stop()
        return result

    def _smt_model_to_sample(self, smt_model):
        sample = ParameterInstantiation()
        for par in self.parameters:
            value = smt_model[par.variable.name]
            rational = pc.Rational(value)
            sample[par] = rational
        return sample

    def _evaluate(self, smt_model):
        sample = self._smt_model_to_sample(smt_model)
        eval_dict = dict([(k.variable, v) for k, v in sample.items()])
        value = self._ratfunc.evaluate(eval_dict)
        logger.debug("Evaluation of sample yields {}".format(value))
        return InstantiationResult(sample, value)
