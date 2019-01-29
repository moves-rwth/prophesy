from prophesy.regions.region_smtchecker import SmtRegionChecker
import prophesy.adapter.pycarl as pc
from prophesy.adapter.pycarl import Constraint, Relation
from prophesy.smt.smt import VariableDomain
from prophesy.data.samples import ParameterInstantiation, InstantiationResult
from prophesy.data.property import OperatorType
import logging
import time

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
        self.threshold_set = False

    def initialize(self, problem_description, constants=None, fixed_threshold = True, fixed_direction = None):
        """
        Initializes the smt solver to consider the problem at hand.

        :param problem_description: 
        :type problem_description: ProblemDescription
        :param threshold:
        """
        if fixed_direction is not None:
            if fixed_direction not in ["safe", "bad"]:
                raise ValueError("Direction can only be fixed to safe or bad")
            self._fixed_direction = fixed_direction
        self.fixed_threshold = fixed_threshold
        lower_bounded_variables = True
        upper_bounded_variables = False
        assert problem_description.solution_function is not None
        assert problem_description.parameters is not None
        if self.fixed_threshold:
            assert problem_description.threshold is not None

        encoding_start = time.time()
        #TODO expanding might be a stupid idea.
        self._ratfunc = pc.expand(problem_description.solution_function)
        self.parameters = problem_description.parameters

        for p in self.parameters:
            self._smt2interface.add_variable(p.name, VariableDomain.Real)

        safeVar = pc.Variable("?_safe", pc.VariableType.BOOL)
        badVar = pc.Variable("?_bad", pc.VariableType.BOOL)
        self._thresholdVar = pc.Variable("T")
        rf1Var = pc.Variable("rf1")
        rf2Var = pc.Variable("rf2")



        self._smt2interface.add_variable(safeVar.name, VariableDomain.Bool)
        self._smt2interface.add_variable(badVar.name, VariableDomain.Bool)
        self._smt2interface.add_variable(self._thresholdVar.name, VariableDomain.Real)

        #Fix direction after declaring variables
        if self._fixed_direction is not None:
            excluded_dir = "safe" if self._fixed_direction == "bad" else "bad"
            # Notice that we have to flip the values, as we are checking all-quantification
            self._smt2interface.fix_guard("?_" + self._fixed_direction, False)
            self._smt2interface.fix_guard("?_" + excluded_dir, True)

        #TODO denominator unequal constant.
        if pc.denominator(self._ratfunc) != 1:
            for constraint in problem_description.welldefined_constraints:
                if not constraint.lhs.total_degree <= 1 or constraint.relation == pc.Relation.NEQ:
                    raise RuntimeError("Non-linear well-definednessconstraints are not supported right now")
            # We do know now that the well-defined points are connected.
            sample = self._get_welldefined_point(problem_description.welldefined_constraints)
            value = pc.denominator(self._ratfunc).evaluate(sample)
            self._smt2interface.add_variable(rf1Var.name, VariableDomain.Real)
            self._smt2interface.add_variable(rf2Var.name, VariableDomain.Real)
            if upper_bounded_variables and problem_description.property.operator == OperatorType.probability:
                self._smt2interface.assert_constraint(pc.Constraint(pc.Polynomial(rf1Var) - rf2Var, pc.Relation.LESS))
            if value < 0:
                if lower_bounded_variables:
                    self._smt2interface.assert_constraint(pc.Constraint(rf1Var, pc.Relation.LESS, pc.Rational(0)))
                    self._smt2interface.assert_constraint(pc.Constraint(rf2Var, pc.Relation.LESS, pc.Rational(0)))

                safe_constraint = Constraint(pc.Polynomial(rf1Var) - self._thresholdVar * rf2Var, self._bad_relation)
                bad_constraint = Constraint(pc.Polynomial(rf1Var) - self._thresholdVar * rf2Var, self._safe_relation)
            else:
                if lower_bounded_variables:
                    self._smt2interface.assert_constraint(pc.Constraint(rf1Var, pc.Relation.GREATER, pc.Rational(0)))
                    self._smt2interface.assert_constraint(pc.Constraint(rf2Var, pc.Relation.GREATER, pc.Rational(0)))

                safe_constraint = Constraint(pc.Polynomial(rf1Var) - self._thresholdVar * rf2Var, self._safe_relation)
                bad_constraint = Constraint(pc.Polynomial(rf1Var) - self._thresholdVar * rf2Var, self._bad_relation)
            rf1_constraint = Constraint(pc.Polynomial(rf1Var) - pc.numerator(self._ratfunc), Relation.EQ)
            rf2_constraint = Constraint(pc.Polynomial(rf2Var) - pc.denominator(self._ratfunc), Relation.EQ)
            self._smt2interface.assert_constraint(rf1_constraint)
            self._smt2interface.assert_constraint(rf2_constraint)
        else:
            safe_constraint = Constraint(pc.numerator(self._ratfunc) - pc.Polynomial(self._thresholdVar), self._safe_relation)
            bad_constraint = Constraint(pc.numerator(self._ratfunc) - pc.Polynomial(self._thresholdVar), self._bad_relation)

        self._smt2interface.assert_guarded_constraint("?_safe", safe_constraint)
        self._smt2interface.assert_guarded_constraint("?_bad", bad_constraint)
        if self.fixed_threshold:
            self._add_threshold_constraint(problem_description.threshold)
        self._encoding_timer += time.time() - encoding_start

    def change_threshold(self, new_threshold):
        assert self.fixed_threshold is not True
        #TODO check that the interface is at the level where we pushed the threshold.
        if self.threshold_set:
            self._smt2interface.pop()
        self._smt2interface.push()
        self._add_threshold_constraint(new_threshold)
        self.threshold_set = True

    def _add_threshold_constraint(self, threshold):
        threshold_constraint = pc.Constraint(pc.Polynomial(self._thresholdVar) - threshold,
                                             pc.Relation.EQ)
        self._smt2interface.assert_constraint(threshold_constraint)


    def _get_welldefined_point(self, constraints):
        extrasmt2 = type(self._smt2interface)()
        extrasmt2.run()
        for p in self.parameters:
            extrasmt2.add_variable(p.name, VariableDomain.Real)
        for constraint in constraints:
            extrasmt2.assert_constraint(constraint)
        extrasmt2.check()
        smt_model = extrasmt2.get_model()
        result = self._smt_model_to_sample(smt_model)
        extrasmt2.stop()
        return result

    def _smt_model_to_sample(self, smt_model):
        sample = ParameterInstantiation()
        try:
            for par in self.parameters:
                value = smt_model[par.name]
                rational = pc.Rational(value)
                sample[par] = rational
        except ValueError:
            logger.debug("Cannot translate into a rational instance")
            return None
        return sample

    def _evaluate(self, smt_model):
        logger.debug("Evaluate model obtained by SMT solver")
        sample = self._smt_model_to_sample(smt_model)
        logger.debug("Model is %s", sample)
        value = self._ratfunc.evaluate(sample)
        logger.debug("Evaluation of sample yields {}".format(value))
        return InstantiationResult(sample, value)
