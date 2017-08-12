import logging

from prophesy.regions.region_smtchecker import SmtRegionChecker
from prophesy.modelcheckers.stormpy import StormpyModelChecker
import prophesy.adapter.stormpy as sp
import prophesy.adapter.pycarl as pc
from prophesy.smt.smt import VariableDomain
from prophesy.data.samples import ParameterInstantiation, ParameterInstantiations, InstantiationResult
from prophesy.data.property import Property, OperatorType

logger = logging.getLogger(__name__)


class EtrRegionChecker(SmtRegionChecker):
    """
    Directly encodes the property in ETR. 
    """

    def __init__(self, backend):
        """
        
        :param backend: 
        """
        super().__init__(backend)
        self.model_explorer = StormpyModelChecker()

    def initialize(self, problem_description, threshold, constants=None):
        """
        
        :param problem_description: 
        :type problem_description: 
        :param threshold: 
        :param constants: 
        :return: 
        """
        _bounded_variables = True  # Add bounds to all state variables.

        if problem_description.model is None:
            raise ValueError("ETR checker requires the model as part of the problem description")

        safeVar = pc.Variable("__safe", pc.VariableType.BOOL)
        badVar = pc.Variable("__bad", pc.VariableType.BOOL)
        thresholdVar = pc.Variable("T")

        self.parameters = problem_description.parameters
        for par in self.parameters:
            self._smt2interface.add_variable(par.variable.name)

        self._smt2interface.add_variable(safeVar, VariableDomain.Bool)
        self._smt2interface.add_variable(badVar, VariableDomain.Bool)
        self._smt2interface.add_variable(thresholdVar, VariableDomain.Real)

        self.model_explorer.load_model_from_prismfile(problem_description.model)
        self.model_explorer.set_pctl_formula(problem_description.property)
        model = self.model_explorer.get_model()

        if model.model_type != sp.ModelType.DTMC:
            raise RuntimeError("Only DTMCs are supported for now.")

        if len(model.initial_states) > 1:
            raise NotImplementedError("We only support models with a single initial state")
        if len(model.initial_states) == 0:
            raise RuntimeError("We only support models with an initial state.")

        if problem_description.property.operator == OperatorType.probability:
            prob0, prob1 = self._find_prob01_states(self.model_explorer.pctlformula[0], model)

            initial_state_var = None
            state_var_mapping = dict()
            for state in model.states:
                if prob0.get(state.id):
                    continue
                if prob1.get(state.id):
                    continue
                stateVar = pc.Variable("s_" + str(state))
                state_var_mapping[state.id] = stateVar
                self._smt2interface.add_variable(stateVar, VariableDomain.Real)
                if state.id in model.initial_states:
                    initial_state_var = stateVar
            if initial_state_var is None:
                # TODO
                raise RuntimeError("Initial state is a prob0/prob1 state. Currently not supported")
        else:
            assert problem_description.property.operator == OperatorType.reward
            raise NotImplementedError("Rewards are not yet supported")

        safe_constraint = pc.Constraint(pc.Polynomial(initial_state_var) - thresholdVar, self._safe_relation)
        bad_constraint = pc.Constraint(pc.Polynomial(initial_state_var) - thresholdVar, self._bad_relation)
        self._smt2interface.assert_guarded_constraint("__safe", safe_constraint)
        self._smt2interface.assert_guarded_constraint("__bad", bad_constraint)
        threshold_constraint = pc.Constraint(pc.Polynomial(thresholdVar) - threshold, pc.Relation.EQ)
        self._smt2interface.assert_constraint(threshold_constraint)

        if problem_description.property.operator == OperatorType.probability:
            for state in model.states:
                state_var = state_var_mapping.get(state.id)
                if state_var is None:
                    continue
                if _bounded_variables:
                    self._smt2interface.assert_constraint(pc.Constraint(state_var, pc.Relation.GREATER, pc.Rational(0)))
                    self._smt2interface.assert_constraint(pc.Constraint(state_var, pc.Relation.LESS, pc.Rational(1)))
                state_equation = -pc.Polynomial(state_var)
                for action in state.actions:
                    for transition in action.transitions:
                        denom = pc.denominator(pc.convert_from(transition.value()))
                        if not denom.is_constant():
                            raise RuntimeError("only polynomial constraints are supported right now.")
                        denom = denom.constant_part()

                        value = pc.numerator(pc.convert_from(transition.value()))
                        if not value.is_constant():
                            value = value.polynomial() * (1 / denom)
                        else:
                            value = pc.Polynomial(value.constant_part()) / denom

                        if prob0.get(transition.column):
                            continue
                        if prob1.get(transition.column):
                            state_equation = state_equation + value
                            continue
                        state_equation = state_equation + value * state_var_mapping.get(transition.column)
                logger.debug(state_equation)
                state_constraint = pc.Constraint(state_equation, pc.Relation.EQ)
                self._smt2interface.assert_constraint(state_constraint)
        else:
            raise NotImplementedError("Rewards are not yet supported")

    def _find_prob01_states(self, property, model):
        formula = property.raw_formula
        assert type(formula) == sp.logic.ProbabilityOperator
        path_formula = formula.subformula
        if type(path_formula) == sp.logic.EventuallyFormula:
            phi_formula = sp.logic.BooleanLiteralFormula(True)
            psi_formula = path_formula.subformula
        elif type(path_formula) == sp.logic.UntilFormula:
            phi_formula = path_formula.subformula[0]
            psi_formula = path_formula.subformula[1]
        else:
            raise ValueError("Property type not supported")
        phi_result = sp.model_checking(model, phi_formula)
        phi_states = phi_result.get_truth_values()
        psi_result = sp.model_checking(model, psi_formula)
        psi_states = psi_result.get_truth_values()
        (prob0, prob1) = sp.compute_prob01_states(model, phi_states, psi_states)
        return prob0, prob1

    def _find_rew0_states(self, property, model):
        formula = property.raw_formula
        assert type(formula) == sp.logic.RewardOperator
        path_formula = formula.subformula
        if type(path_formula) == sp.logic.EventuallyFormula:
            phi_formula = sp.logic.BooleanLiteralFormula(True)
            psi_formula = path_formula.subformula
        else:
            raise ValueError("Property type not supported")
        phi_result = sp.model_checking(model, phi_formula)
        phi_states = phi_result.get_truth_values()
        psi_result = sp.model_checking(model, psi_formula)
        psi_states = psi_result.get_truth_values()
        (prob0, prob1) = sp.compute_prob01_states(model, phi_states, psi_states)
        return prob0, prob1

    def _evaluate(self, smt_model):
        sample = ParameterInstantiation()
        for par in self.parameters:
            value = smt_model[par.variable.name]
            rational = pc.Rational(value)
            sample[par] = rational
        samples = ParameterInstantiations()
        samples.append(sample)
        samples.parameters = self.parameters
        value = self.model_explorer.perform_sampling(samples).get(sample)

        return InstantiationResult(sample, value)