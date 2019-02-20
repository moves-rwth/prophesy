import logging
import time

from prophesy.regions.region_smtchecker import SmtRegionChecker, Context
import prophesy.adapter.stormpy as sp
import prophesy.adapter.pycarl as pc
from prophesy.smt.smt import VariableDomain
from prophesy.data.samples import ParameterInstantiation, InstantiationResult
from prophesy.data.property import Property, OperatorType, OperatorDirection

logger = logging.getLogger(__name__)


class EtrRegionChecker(SmtRegionChecker):
    """
    Directly encodes the property in ETR. 
    """

    def __init__(self, backend, mc):
        """
        Constructor.
        :param backend: 
        """
        super().__init__(backend)
        self.model_explorer = mc
        self.fixed_threshold = True
        self.threshold_set = False
        self._threshold = None
        self._safe_transition_relation = pc.Relation.GEQ
        self._bad_transition_relation = pc.Relation.LEQ
        self._state_var_mapping = None
        self._exact = True
        self._additional_constraints = False
        self._safe_demonic = None
        self._smt2interface_bad = None
        # When checking MDPs for safe regions, take the demonic relation.
        # For the bad region, we thus take the angelic relation

    def over_approximates(self):
        return not self._exact

    def _getsolver(self, safe):
        # flip flag to search for contrary
        if self._smt2interface_bad is not None:
            if not safe:
                logger.debug("Use SMT/Safe ETR solver; demonic encoding: {}".format(self._safe_demonic))
                return Context(self._smt2interface, True)
            else:
                logger.debug("Use SMT/Bad ETR solver; demonic encoding: {}".format(not self._safe_demonic))
                return Context(self._smt2interface_bad, True)
        else:
            return Context(self._smt2interface, self._fixed_direction)

    def _make_constraint(self, lhs, rel):
        # TODO add smarter checks for rational functions
        if type(lhs) == pc.Polynomial:
            return pc.Constraint(lhs, rel)
        else:
            assert type(lhs) == pc.RationalFunction
            if rel == pc.Relation.EQ or lhs.denominator.is_constant():
                return pc.Constraint(lhs.numerator,rel)
            else:
                raise NotImplementedError("We focussed on simple cases so far.")


    def _add_state_constraint(self, equations, model_type, id):
        if model_type == sp.ModelType.DTMC:
            assert len(equations) == 1
            state_constraint = self._make_constraint(equations[0], pc.Relation.EQ)
            self._smt2interface.assert_guarded_constraint("?_exact", state_constraint,  name="state_outgoing_{}".format(id))

        elif model_type == sp.ModelType.MDP and self._safe_demonic:
            # safe gets demonic encoding
            safe_action_constraint = pc.Formula(pc.FormulaType.OR, [pc.Formula(self._make_constraint(action_equation, pc.Relation.EQ)) for action_equation in equations])
            self._smt2interface.assert_guarded_constraint("?_safe", safe_action_constraint)
            for action_equation in equations:
                # bad gets angelic encoding
                bad_action_constraint = self._make_constraint(action_equation, self._bad_transition_relation)
                self._smt2interface_bad.assert_guarded_constraint("?_bad", bad_action_constraint)

        elif model_type == sp.ModelType.MDP and not self._safe_demonic:
            bad_action_constraint = pc.Formula(pc.FormulaType.OR, [pc.Formula(self._make_constraint(action_equation, pc.Relation.EQ)) for action_equation in equations])
            self._smt2interface_bad.assert_guarded_constraint("?_bad", bad_action_constraint)
            for action_equation in equations:
                safe_action_constraint = self._make_constraint(action_equation, self._safe_transition_relation)
                self._smt2interface.assert_guarded_constraint("?_safe", safe_action_constraint)

    def _add_variable_to_smtinterfaces(self, name, tp):
        self._smt2interface.add_variable(name, tp)
        if self._smt2interface_bad:
            self._smt2interface_bad.add_variable(name, tp)


    def _assert_constraint(self, constraint):
        self._smt2interface.assert_constraint(constraint)
        if self._smt2interface_bad:
            self._smt2interface_bad.assert_constraint(constraint)

    def _assert_guarded_constraint(self, guard, constraint):
        self._smt2interface.assert_guarded_constraint(guard, constraint)
        if self._smt2interface_bad:
            self._smt2interface_bad.assert_guarded_constraint(guard, constraint)

    def _fix_guard(self, guard, val):
        self._smt2interface.fix_guard(guard, val)
        if self._smt2interface_bad:
            self._smt2interface_bad.fix_guard(guard, val)


    def initialize(self, problem_description, fixed_threshold = True, fixed_direction = None):
        """
        
        :param problem_description: 
        :type problem_description: 
        :param constants: 
        :return: 
        """

        if self.fixed_threshold:
            if not problem_description.threshold:
                raise ValueError("ETR with fixed threshold needs a threshold")
            else:
                self._threshold = problem_description.threshold
        if problem_description.model is None:
            raise ValueError("ETR checker requires the model as part of the problem description")
        if fixed_direction is not None:
            if fixed_direction not in ["safe", "bad", "border"]:
                raise ValueError("Direction can only be fixed to safe, bad, border")
            self._fixed_direction = fixed_direction
        model = self.model_explorer.get_model()
        _property = Property.from_string(str(self.model_explorer.pctlformula[0].raw_formula)) #TODO ugly :(


        if model.model_type == sp.ModelType.MDP:
            # TODO for logging smt calls, and obtaining proper stats in the cli, this is not a good idea.
            self._smt2interface_bad = type(self._smt2interface)(self._smt2interface.location)
            self._smt2interface_bad.run()
            if _property.operator_direction == OperatorDirection.max:
                self._safe_demonic = True
            else:
                assert _property.operator_direction == OperatorDirection.min
                self._safe_demonic = False


        if len(model.initial_states) > 1:
            raise NotImplementedError("We only support models with a single initial state")
        if len(model.initial_states) == 0:
            raise RuntimeError("We only support models with an initial state.")

        logger.info("Writing equation system to solver")
        self.fixed_threshold = fixed_threshold
        _bounded_variables = True  # Add bounds to all state variables.
        _additional_constraints = self._additional_constraints

        encoding_start = time.time()
        safeVar = pc.Variable("?_safe", pc.VariableType.BOOL)
        badVar = pc.Variable("?_bad", pc.VariableType.BOOL)
        equalsVar = pc.Variable("?_equals", pc.VariableType.BOOL)
        exactVar = pc.Variable("?_exact", pc.VariableType.BOOL)

        self._thresholdVar = pc.Variable("T")

        self.parameters = problem_description.parameters
        for par in self.parameters:
            self._add_variable_to_smtinterfaces(par.name, VariableDomain.Real)

        self._add_variable_to_smtinterfaces(safeVar.name, VariableDomain.Bool)
        self._add_variable_to_smtinterfaces(badVar.name, VariableDomain.Bool)

        self._add_variable_to_smtinterfaces(equalsVar.name, VariableDomain.Bool)
        self._add_variable_to_smtinterfaces(exactVar.name, VariableDomain.Bool)
        self._add_variable_to_smtinterfaces(self._thresholdVar.name, VariableDomain.Real)


        if self._fixed_direction is not None:
            #TODO support this for MDPs
            if model.model_type != sp.ModelType.DTMC:
                raise NotImplementedError("Support for fixed directions and MDPs is not yet present")
            if self._fixed_direction == "border":
                self._smt2interface.fix_guard("?_safe", False)
                self._smt2interface.fix_guard("?_bad", False)
                self._smt2interface.fix_guard("?_equals", True)
            else:
                excluded_dir = "safe" if self._fixed_direction == "bad" else "bad"
                # Notice that we have to flip the values, as we are checking all-quantification
                self._smt2interface.fix_guard("?_" + self._fixed_direction, False)
                self._smt2interface.fix_guard("?_" + excluded_dir, True)
                self._smt2interface.fix_guard("?_equals", False)

        if self._smt2interface_bad:
            self._smt2interface_bad.fix_guard("?_bad", True)
            self._smt2interface_bad.fix_guard("?_safe", False)
            self._smt2interface_bad.fix_guard("?_equals", False)
            self._smt2interface.fix_guard("?_safe", True)
            self._smt2interface.fix_guard("?_bad", False)
            self._smt2interface.fix_guard("?_equals", False)

        if self._exact:
            self._fix_guard("?_exact", True)
        else:
            raise NotImplementedError("Support for inexact solvign for MDPs is not yet present")

        initial_state_var = None
        self._state_var_mapping = dict()

        if _property.operator == OperatorType.probability:
            prob0, prob1 = self.model_explorer.prob01_states()

            for state in model.states:
                if prob0.get(state.id):
                    continue
                if prob1.get(state.id):
                    continue
                stateVar = pc.Variable("s_" + str(state))
                self._state_var_mapping[state.id] = stateVar
                self._add_variable_to_smtinterfaces(stateVar.name, VariableDomain.Real)
                if state.id in model.initial_states:
                    initial_state_var = stateVar
            if initial_state_var is None:
                # TODO
                raise RuntimeError("Initial state is a prob0/prob1 state. Currently not supported")
        else:
            assert _property.operator == OperatorType.reward
            reward_model = self._get_reward_model(model, _property)

            rew0 = self.model_explorer.rew0_states()
            for state in model.states:
                if rew0.get(state.id):
                    continue
                stateVar = pc.Variable("s_" + str(state))
                self._state_var_mapping[state.id] = stateVar
                self._add_variable_to_smtinterfaces(stateVar.name, VariableDomain.Real)
                if state.id in model.initial_states:
                    initial_state_var = stateVar
            if initial_state_var is None:
                raise RuntimeError("Initial state is a reward 0 state. Currently not supported")

        safe_constraint = pc.Constraint(pc.Polynomial(initial_state_var) - self._thresholdVar, self._safe_relation)
        bad_constraint = pc.Constraint(pc.Polynomial(initial_state_var) - self._thresholdVar, self._bad_relation)

        equals_constraint = pc.Constraint(pc.Polynomial(initial_state_var) - self._thresholdVar, self._equals_relation)
        self._assert_guarded_constraint("?_safe", safe_constraint)
        self._assert_guarded_constraint("?_bad", bad_constraint)
        self._assert_guarded_constraint("?_equals", equals_constraint)
        if self.fixed_threshold:
            self._add_threshold_constraint(self._threshold)

        if problem_description.property.operator == OperatorType.probability:
            for state in model.states:
                state_equations = []
                state_var = self._state_var_mapping.get(state.id)
                if state_var is None:
                    continue
                if _bounded_variables:
                    # if bounded variable constraints are to be added, do so.
                    self._assert_constraint(pc.Constraint(state_var, pc.Relation.GREATER, pc.Rational(0)))
                    self._assert_constraint(pc.Constraint(state_var, pc.Relation.LESS, pc.Rational(1)))
                state_equation = -pc.Polynomial(state_var)
                for action in state.actions:
                    action_equation = state_equation
                    for transition in action.transitions:
                        if prob0.get(transition.column):
                            continue
                        # obtain the transition value as a polynomial.
                        if transition.value().is_constant():
                            value = pc.Polynomial(pc.convert_from_storm_type(transition.value().constant_part()))
                        else:
                            denom = pc.denominator(pc.convert_from_storm_type(transition.value()))
                            if not denom.is_constant():
                                denom = denom.constant_part()

                                value = pc.numerator(pc.convert_from_storm_type(transition.value()))
                                value = value.polynomial() * (1 / denom)
                            else:
                                value = pc.expand_from_storm_type(transition.value())


                        if prob1.get(transition.column):
                            action_equation +=  value
                            continue
                        action_equation +=  value * self._state_var_mapping.get(transition.column)
                #logger.debug(state_equation)
                    state_equations.append(action_equation)
                self._add_state_constraint(state_equations, model.model_type, state.id)
            #Nothing left to be done for the model.
        else:
            for state in model.states:
                state_equations = []
                state_var = self._state_var_mapping.get(state.id)
                if state_var is None:
                    continue
                if _bounded_variables:
                    # if bounded variable constraints are to be added, do so.
                    self._assert_constraint(pc.Constraint(state_var, pc.Relation.GREATER, pc.Rational(0)))
                state_reward = pc.expand_from_storm_type(reward_model.state_rewards[state.id])
                if state_reward.is_constant():
                    reward_value = state_reward.constant_part()
                else:
                    denom = pc.denominator(state_reward)
                    if denom.is_constant():
                        denom = denom.constant_part()
                        reward_value = pc.numerator(state_reward) * (1 / denom)
                    else:
                        reward_value = state_reward
                state_equation = -pc.Polynomial(state_var) + reward_value



                for action in state.actions:
                    action_equation = state_equation
                    for transition in action.transitions:

                        if rew0.get(transition.column):
                            continue
                        # obtain the transition value as a polynomial.
                        if transition.value().is_constant():
                            value = pc.Polynomial(pc.convert_from_storm_type(transition.value().constant_part()))
                        else:
                            denom = pc.denominator(pc.convert_from_storm_type(transition.value()))
                            if denom.is_constant():
                                denom = denom.constant_part()

                                value = pc.numerator(pc.convert_from_storm_type(transition.value()))
                                value = value.polynomial() * (1 / denom)
                            else:
                                value = pc.expand_from_storm_type(transition.value())

                        action_equation += value * self._state_var_mapping.get(transition.column)
                #logger.debug(state_equation)
                    state_equations.append(action_equation)

                self._add_state_constraint(state_equations, model.model_type, state.id)
            #Nothing left to be one

        if _additional_constraints and problem_description.property.operator == OperatorType.probability:
            assert model.model_type == sp.ModelType.DTMC
            for state in model.states:
                state_var = self._state_var_mapping.get(state.id)
                if state_var is None:
                    continue
                state_equation = -pc.Polynomial(state_var)
                for action in state.actions:
                    trans = []
                    for transition in action.transitions:
                        if prob0.get(transition.column):
                            continue
                        # obtain the transition value as a polynomial.
                        if transition.value().is_constant():
                            value = pc.Polynomial(pc.convert_from_storm_type(transition.value().constant_part()))
                        else:
                            denom = pc.denominator(pc.convert_from_storm_type(transition.value()))
                            if not denom.is_constant():
                                raise RuntimeError("only polynomial constraints are supported right now.")
                            denom = denom.constant_part()

                            value = pc.numerator(pc.convert_from_storm_type(transition.value()))
                            value = value.polynomial() * (1 / denom)



                        if prob1.get(transition.column):
                            trans.append((None, value))
                        else:
                            trans.append((self._state_var_mapping.get(transition.column), value))

                    prob0, prob1 = self.model_explorer.prob01_states()



                    if len(trans) == 1:
                        if trans[0][0] and trans[0][1] != 1:
                            self._smt2interface.assert_constraint(pc.Constraint(pc.Polynomial(state_var) - trans[0][0], pc.Relation.LESS))
                            self._smt2interface.assert_constraint(pc.Constraint(pc.Polynomial(state_var) - trans[0][1], pc.Relation.LESS))
                            self._smt2interface.assert_constraint(pc.Constraint(pc.Polynomial(state_var) - trans[0][0] - trans[0][1] + pc.Rational(1), pc.Relation.GREATER ))
                    if len(trans) == 2:
                        if trans[0][0] and trans[0][1] != 1 and trans[1][0] and trans[1][1] != 1:
                            self._smt2interface.assert_constraint(pc.Constraint(pc.Polynomial(state_var) - trans[0][0] - trans[1][0], pc.Relation.LESS), name="app2ubstst{}".format(state.id))
                            self._smt2interface.assert_constraint(
                               pc.Constraint(pc.Polynomial(state_var) - trans[0][0] - trans[1][1], pc.Relation.LESS), name="app2ubsttr{}".format(state.id))
                            self._smt2interface.assert_constraint(
                                pc.Constraint(pc.Polynomial(state_var) - trans[0][1] - trans[1][0], pc.Relation.LESS), name="app2ubtrst{}".format(state.id))
                            self._smt2interface.assert_constraint(
                                pc.Constraint(pc.Polynomial(state_var) - trans[0][0] - trans[1][0] + pc.Rational(1),
                                              pc.Relation.GREATER), name="app2lbsttr{}".format(state.id))




                    #Nothing left to be done for the model.

        self._encoding_timer += time.time() - encoding_start


    def change_threshold(self, new_threshold):
        if self._smt2interface_bad:
            raise RuntimeError("Not supported for two smt interfaces (MDP)")
        assert self.fixed_threshold is not True
        #TODO check that the interface is at the level where we pushed the threshold.
        if self.threshold_set:
            self._smt2interface.pop()
        self._smt2interface.push()
        self._add_threshold_constraint(new_threshold)
        self.threshold_set = True
        self._threshold = new_threshold

    def _add_threshold_constraint(self, threshold):
        threshold_constraint = pc.Constraint(pc.Polynomial(self._thresholdVar) - threshold,
                                             pc.Relation.EQ)
        self._assert_constraint(threshold_constraint)



    def _get_reward_model(self, model, _property):
        model.reduce_to_state_based_rewards()
        if _property.reward_name is not None:
            reward_model = model.reward_models[_property.reward_name]
        else:
            if "" in model.reward_models:
                reward_model = model.reward_models[""]
            else:
                if len(model.reward_models) > 1:
                    raise RuntimeError("Unclear reference to reward model. Please specify a name.")
                reward_model = list(model.reward_models.values())[0]
        assert not reward_model.has_state_action_rewards
        assert not reward_model.has_transition_rewards
        return reward_model


    def _evaluate(self, smt_model):
        sample = ParameterInstantiation()
        for par in self.parameters:
            value = smt_model[par.name]
            rational = pc.Rational(value)
            sample[par] = rational
        value = self.model_explorer.perform_sampling([sample])[sample]

        return InstantiationResult(sample, value)
