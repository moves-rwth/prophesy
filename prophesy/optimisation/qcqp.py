from __future__ import division
import stormpy
import stormpy.core
import stormpy.logic
import stormpy.pars
import time
import math
from gurobipy import *
from prophesy.data.property import OperatorType

import prophesy.adapter.pycarl as pc
from prophesy.data.samples import ParameterInstantiation, InstantiationResult

class QcqpOptions():
    def __init__(self, mu, maxiter, graph_epsilon, silent, incremental, all_welldefined,
                 store_quadratic, mc_termination_check, intermediate_mc, minimise_violation):
        self.mu = 0.05
        #self.mu_multiplicator = 10
        self.maxiter = maxiter
        self.graph_epsilon = graph_epsilon
        self.silent = silent
        self.incremental = incremental
        self.all_welldefined = all_welldefined
        self.store_quadratic = store_quadratic
        self.mc_termination_check = mc_termination_check
        self.intermediate_mc = intermediate_mc
        self.minimise_violation = minimise_violation
        if not self.incremental and self.store_quadratic:
            raise RuntimeError("Store quadratic can only be set for incremental qcqp.")
        if self.intermediate_mc and self.mc_termination_check:
            raise RuntimeError("Mc termination checks and intermediate MC are mutually exclusive")


class QcqpResult():
    def __init__(self, value_at_initial, parameter_values):
        self.value_at_initial = value_at_initial
        self.parameter_values = parameter_values

class UnpackedTransition:
    def __init__(self):
        self.constant = None
        self.variable_dependent_numerator = None
        self.inverse_denominator = None

    def is_constant(self):
        return self.variable_dependent_numerator is None

gurobi_status = {1: "not executed", 2: "solved", 3: "infeasible"}

class QcqpSolver():
    def __init__(self, evaluator, mc_check):
        self.solver_timer = 0.0
        self.encoding_timer = 0.0
        self.iterate_timer = 0.0
        self.iterations = 0
        self._parameters = None
        self._prob0E = None
        self._prob1A = None
        self._encoding = None
        self._pVars = None
        self._tau = None
        self._paramVars = None
        self._tt = None
        self._paraminit = None
        self._pinit = None
        self._pexpr = None
        self._mu = None
        self._constants_floats = dict()
        self._auxtimer1 = 0.0
        self._auxtimer2 = 0.0
        self._auxtimer3 = 0.0
        self._states_and_transitions = None
        self._quadratic_states_and_transitions = None
        self._evaluate = evaluator
        self._mc_check = mc_check
        self._reward_model = None
        self._property_type = None
        self._lower_state_bounds = None
        self._upper_state_bounds = None

    def _check_prob0(self, state):
        return self._prob0E.get(state)

    def _check_prob1(self, state):
        if self._is_reward_property:
            return False
        return self._prob1A.get(state)

    def _make_unpacked_transition(self, transition_value):
        ut = UnpackedTransition()
        if transition_value.is_constant():
            ut.constant = self._float_repr(transition_value.constant_part())
        else:
            # Denominator of transition
            den = transition_value.denominator
            assert den.is_constant()
            if den.is_one():
                ut.inverse_denominator = 1.0
            else:
                ut.inverse_denominator = 1 / self._float_repr(den.constant_part())
            num = self._numerator(transition_value)
            ut.variable_dependent_numerator = num - num.constant_part
            ut.constant = self._float_repr(num.constant_part) * ut.inverse_denominator
        return ut

    def _compute_states_and_transitions(self, model):
        self._states_and_transitions = []
        for row_group in range(model.nr_states):
            self._states_and_transitions.append((row_group,[]))
            for row in range(model.transition_matrix.get_row_group_start(row_group),
                             model.transition_matrix.get_row_group_end(row_group)):
                self._states_and_transitions[-1][1].append(([], 0))
                for entry in model.transition_matrix.get_row(row):
                    if not self._check_prob0(entry.column):
                        self._states_and_transitions[-1][1][-1][0].append((self._make_unpacked_transition(entry.value()), entry.column))

    def _solve_model(self):
        start3 = time.time()
        # Solves the problem
        print('Solving...')
        try:
            self._encoding.optimize()
        except GurobiError:
            raise RuntimeError("Gurobi throws an error")
        print("Gurobi reports: " + gurobi_status[self._encoding.status] if self._encoding.status in gurobi_status else "Unknown")
        t3 = time.time()
        self.solver_timer += (t3 - start3)
        print("Solver time :" + str(t3 - start3))

    def _numerator(self, transition_value):
        return transition_value.numerator.polynomial()

    def _prob01constraints(self, model):
        for state in range(model.nr_states):
            if self._check_prob1(state):
                self._encoding.addConstr(self._pVars[state] == 1)
            elif self._check_prob0(state):
                self._encoding.addConstr(self._pVars[state] == 0)

    def _create_encoding(self, model, options, lower_state_bounds=None, upper_state_bounds=None):
        numstate = model.nr_states

        self._encoding = Model("qcp")
        self._encoding.setParam('OutputFlag', not options.silent)
        self._encoding.setParam(GRB.Param.BarHomogeneous, 1.0)

        # Initializing gurobi variables for parameters,lb=lowerbound, ub=upperbound
        if lower_state_bounds is None and upper_state_bounds is None:
            if self._is_reward_property:
                self._pVars = [self._encoding.addVar(lb=0) for _ in range(numstate)]
            else:
                self._pVars = [self._encoding.addVar(lb=0, ub=1.0) for _ in range(numstate)]
        else:
            assert lower_state_bounds is not None
            assert upper_state_bounds is not None
            self._pVars = [self._encoding.addVar(lb=lower_state_bounds.at(state) if lower_state_bounds.at(state) < math.inf else 0.0, ub=upper_state_bounds.at(state)) for state in range(numstate)]

        self._tau = [self._encoding.addVar(lb=0) for _ in range(numstate)]
        self._tt = self._encoding.addVar(lb=0.0, name="TT")
        self._paramVars = dict([[x.id, self._encoding.addVar(lb=i.left_bound(), ub=i.right_bound())] for x, i in self._parameters.items()])

        # Updates the model for gurobi
        self._encoding.update()

    def _float_repr(self, constant_val):
        """
        Returns the float representation for a constant value
        :param constant_val: 
        :return: 
        """
        if constant_val.is_one():
            return 1.0
        elif constant_val.is_minus_one():
            return -1.0
        v = self._constants_floats.get(constant_val, float(constant_val))
        self._constants_floats[constant_val] = v
        return v

    def _get_reward_model(self, model, reward_name):
        model.reduce_to_state_based_rewards()
        if reward_name is not None:
            reward_model = model.reward_models[reward_name]
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

    def _wdconstraints(self, model, options):
        """
        Adds the well-definedness constraints 
        :param model: 
        :param options: 
        :return: 
        """
        if options.all_welldefined:
            # If all parameter instantiations are welldefined, there is no need to add this.
            return
        for state in model.states:

            cons = 0
            for action in state.actions:

                for transition in action.transitions:
                    cons1 = 0.0
                    transition_value = transition.value()
                    den = transition_value.denominator.constant_part()
                    # If the transition value is not a constant
                    if not transition_value.is_constant():
                        num = transition_value.numerator.polynomial()

                        for t in num:
                            # Adds the value of the transition
                            if t.is_constant():
                                cons1 += float(t.coeff) / float(den)
                            # Adds the value of the transition
                            else:
                                if t.tdeg > 1:
                                    raise RuntimeError("We expect the term to be a single variable")
                                param_id = t.monomial[0][0].id
                                coeff = float(t.coeff)

                                cons1 = cons1 + coeff * self._paramVars[param_id] / float(den)
                    # If the transition has parameters, constrain each transition to between 0 and 1
                    if not isinstance(cons1, float):
                        # print(cons1)
                        self._encoding.addConstr(cons1 >= 0 + options.graph_epsilon)
                        self._encoding.addConstr(cons1 <= 1 - options.graph_epsilon)

    def _modelconstraints_reward(self, model, state):
        if not self._is_reward_property:
            return 0.0
        reward_at_state = self._reward_model.get_state_reward(int(state))
        if reward_at_state.is_constant():
            return self._float_repr(reward_at_state.constant_part())


        cons = 0.0
        assert reward_at_state.denominator.is_constant()
        den = self._float_repr(reward_at_state.denominator.constant_part())
        assert den != 0
        for term in reward_at_state.numerator.polynomial():
            if not term.is_constant():
                param_id = term.monomial[0][0].id
                cons += self._float_repr(term.coeff) * self._paramVars[param_id] / den
            else:
                cons += self._float_repr(term.coeff) / den
        return cons

    def _modelconstraints(self, model, dir, options, only_quadratic=False):
        """
        Adds the constraints originating from the model.
        
        :param model: 
        :param options: 
        :param only_quadratic: 
        :return: 
        """
        for state, actions in self._states_and_transitions:
            assert len(actions) == 1
            for entries, l_part_cons in actions:
                # Cons=values constraints on the right hand side for a pdtmc
                # A flag for linear vs quadratic constraints
                q_part_cons = 0
                assert l_part_cons == 0
                if not options.store_quadratic or not options.incremental:
                    l_part_cons += self._modelconstraints_reward(model, state)

                for value,column in entries:
                    l_cons, q_cons = self._modelconstraint_transition(state, (value,column), dir, only_quadratic and options.store_quadratic)
                    if q_cons is not None:
                        q_part_cons += q_cons
                    if not options.store_quadratic or not options.incremental:
                        l_part_cons += l_cons

                # If the constraint is quadratic, add a penalty term to the constraints, otherwise dont add the term
                if not isinstance(q_part_cons, int):
                    start_t = time.time()
                    if dir == "above":
                        self._encoding.addQConstr(self._pVars[state] <= l_part_cons + q_part_cons - self._tau[state])
                    else:
                        self._encoding.addQConstr(self._pVars[state] >= l_part_cons + q_part_cons - self._tau[state])
                    self._auxtimer3 += time.time() - start_t

                elif not only_quadratic:
                    if dir == "above":
                        self._encoding.addConstr(self._pVars[state] <= l_part_cons)
                    else:
                        self._encoding.addConstr(self._pVars[state] >= l_part_cons)


    def _modelconstraints_store(self, model, dir, options):
        quadratic_states_and_transitions = []
        for state, actions in self._states_and_transitions:
            assert len(actions) == 1
            quadratic_entries = []
            for entries, _ in actions:
                # Cons=values constraints on the right hand side for a pdtmc
                l_part_cons = 0
                # A flag for linear vs quadratic constraints
                q_part_cons = 0

                l_part_cons += self._modelconstraints_reward(model, state)

                q_entries = []
                for value, column in entries:
                    l_cons, q_cons = self._modelconstraint_transition(state, (value, column), dir)
                    if q_cons is not None:
                        q_part_cons += q_cons
                        q_entries.append((value, column))
                    l_part_cons += l_cons
                # If the constraint is quadratic, add a penalty term to the constraints, otherwise dont add the term
                if not isinstance(q_part_cons, int):
                    quadratic_entries.append((q_entries, l_part_cons))
                    if dir == "above":
                        self._encoding.addQConstr(self._pVars[state] <= l_part_cons + q_part_cons - self._tau[state])
                    else:
                        self._encoding.addQConstr(self._pVars[state] >= l_part_cons + q_part_cons - self._tau[state])
                else:
                    if dir == "above":
                        self._encoding.addConstr(self._pVars[state] <= l_part_cons)
                    else:
                        self._encoding.addConstr(self._pVars[state] >= l_part_cons)
            if len(quadratic_entries) > 0:
                quadratic_states_and_transitions.append((state, quadratic_entries))
        #print("{} vs {}".format(len(self._states_and_transitions), len(quadratic_states_and_transitions)))
        self._states_and_transitions = quadratic_states_and_transitions

    def _modelconstraint_transition(self, state, transition, dir, only_quadratic=False):
        """
        
        :param state: 
        :param transition: UnpackedTransitions
        :return: linear and quadratic part of the constraints
        """
        assert isinstance(transition[0], UnpackedTransition)
        #linear part of the constraints
        l_cons = 0
        #quadratic part of the constraints
        q_cons = None
        succ = int(transition[1])
        # Value of transition
        transition_value = transition[0]
        assert not self._check_prob0(succ)
        proc_start = time.time()
        # Handle the constant part
        if not only_quadratic:
            # Get the value of transition
            constant_value = transition_value.constant
            # If successor state is prob1, just add the value of transition
            if self._check_prob1(succ):
                l_cons += constant_value
            # Else, add transitionvalue*p_succ
            else:
                l_cons += constant_value * self._pVars[succ]

        # If the transition value is not constant
        if not transition_value.is_constant():
            # Denominator of transition
            denom1 = transition_value.inverse_denominator
            num = transition_value.variable_dependent_numerator
            statevar = self._pVars[succ]
            q_cons = 0.0

            # Iterates over terms in numerators
            for t in num:

                # If the transition term is a constant
                assert not t.is_constant()
                assert t.tdeg <= 1, "We expect the term to be a single variable"
                param_id = t.monomial[0][0].id

                coeff = self._float_repr(t.coeff)

                # Adds transitionvalue*parameter_variable to the constraint if the successor is prob1
                if not only_quadratic and self._check_prob1(succ):
                    l_cons += coeff * self._paramVars[param_id] * denom1
                # Add the quadratic term to the constraints
                else:
                    pinit_succ = self._pinit[succ]
                    paramvar = self._paramVars[param_id]
                    assert self._pexpr is not None
                    pexpr = self._pexpr[param_id]
                    coeff_times_denom = coeff * denom1
                    check_t = time.time()

                    negative_case = (dir == "above" and coeff > 0) or (dir == "below" and coeff < 0)


                    # The bilinear terms are split into convex+concave terms, then the concave term is underapproximated by a affine term
                    # First term in the addition is the affine term, second term is the convex term
                    if negative_case:
                        q_cons += -coeff_times_denom * (0.5 * (pinit_succ) ** 2 -pinit_succ * statevar + pexpr)
                        c = LinExpr([1.0, -1.0], [statevar, paramvar])
                        q_cons += -coeff_times_denom * 0.5 * c * c
                    else:
                        q_cons += LinExpr(coeff_times_denom) * (LinExpr(0.5 * (pinit_succ) ** 2) - pinit_succ * statevar + pexpr)
                        c = LinExpr([1.0, 1.0], [statevar, paramvar])
                        q_cons += coeff_times_denom * 0.5 * c * c
                    self._auxtimer1 += time.time() - check_t

        self._auxtimer2 += time.time() - proc_start
        return l_cons, q_cons

    def _set_objective(self, model, initstate, dir, options):
        """
        Sets the objective to be used for optimisation
        
        :param model: 
        :param initstate: 
        :param options: 
        :return: 
        """
        numstate = model.nr_states
        objective = 0.0
        # Adding terms to the objective
        if options.minimise_violation:
            for state in range(numstate):
                # This minimizes sum of violation,
                objective += self._tau[state]
        else:
            objective += self._tt
        #Maximize the probability of initial state
        if dir == "below":
            for state in range(numstate):
                objective += self._pVars[state]/self._mu
        else:
            for state in range(numstate):
               objective -= self._pVars[state]/self._mu
        self._encoding.setObjective(objective, GRB.MINIMIZE)

    def _violation_constraints(self, model, options):
        """
        Constraints to limit the violation
        
        :param model: 
        :param options: 
        :return: 
        """
        if not options.minimise_violation:
            for state in range(model.nr_states):
                # This constraints minimizes the max of violation
                self._encoding.addConstr(self._tau[state] <= self._tt)

    def _mc(self, threshold, initstate, dir, options):
        """
        Model checking based on the values found by QCQP
        :param threshold: 
        :param initstate: 
        :param options: 
        :return: 
        """
        if options.mc_termination_check:
            param_values = dict([[id, param_var.x] for id, param_var in self._paramVars.items()])
            sample, eval_res = self._evaluate(param_values)
            print(float(eval_res[sample]))

            if dir == "below" and float(eval_res[sample]) < threshold:
                return QcqpResult(self._pVars[initstate].x, param_values), None
            elif dir == "above" and float(eval_res[sample]) > threshold:
                return QcqpResult(self._pVars[initstate].x, param_values), None
        elif options.intermediate_mc:
            param_values = dict([[id, param_var.x] for id, param_var in self._paramVars.items()])
            mc_results = self._mc_check(param_values)
            print(mc_results.at(initstate))
            if dir == "below" and mc_results.at(initstate) < threshold:
                return QcqpResult(self._pVars[initstate].x, param_values), None
            elif dir == "above" and mc_results.at(initstate) > threshold:
                return QcqpResult(self._pVars[initstate].x, param_values), None
            else:
                return None, mc_results
        return None, None

    def _update_pinit(self, mc_result):
        if mc_result is not None:
            assert len(mc_result.get_values()) == len(self._pinit)
            for state in range(len(self._pinit)):
                self._pinit[state] = max(0, mc_result.at(state))
        else:
            for state in range(len(self._pinit)):
                if abs(self._pVars[state].x) > 1e-8:
                    self._pinit[state] = self._pVars[state].x
                else:
                    self._pinit[state] = 0

    def _initialize_pinit(self, nr_states, default_val, force_default=True):
        #if not force_default and self._lower_state_bounds is not None and self._upper_state_bounds is not None:
        #    self._pinit = [min(max(default_val,self._lower_state_bounds.at(state)), self._upper_state_bounds.at(state)) for state in range(nr_states)]
        #else:
        self._pinit = [default_val for _ in range(nr_states)]

    @property
    def _is_reward_property(self):
        return self._property_type == "reward"

    def run(self, model, parameters, prob0E, prob1A, threshold, direction, options, property_type, reward_name = None, lower_state_bounds=None, upper_state_bounds=None):
        """
        Runs the QCQP procedure by a series of calls to gurobi.

        :param model: The model
        :type model: a stormpy dtmc/mdp
        :param parameters: The parameters occuring in the model
        :type parameters: a list of pycarl variables
        :param prob0E: States with a zero probability to the target
        :type: BitVector
        :param prob1A: States with a one probability to the target
        :type: BitVector
        :param threshold: The threshold
        :type threshold: float
        :param direction: Are we looking for a value below or above
        :type direction: a string, either "above" or "below"
        :param options: Further options with which the algorithm should run
        :return: 
        """
        assert direction in ["above", "below"]
        assert property_type in ["probability", "reward"]
        self._prob0E = prob0E
        self._prob1A = prob1A
        self._parameters = parameters
        self._lower_state_bounds = lower_state_bounds
        self._upper_state_bounds = upper_state_bounds
        self._compute_states_and_transitions(model)
        self._property_type = property_type
        if property_type == "reward":
            self._reward_model = self._get_reward_model(model, reward_name)

        if not options.silent:
            print("Number of states: {}".format(model.nr_states))
            print("Number of transitions: {}".format(model.nr_transitions))
            print("Number parameters: {}".format(len(parameters)))
            print("Labels: {}".format(model.labeling.get_labels()))
            print(model.model_type)

        # Initializing some arrays for state, parameter and tau variables, and their values at previous iterations
        self._paraminit = dict([[x.id, 0.5] for x in parameters])
        self._initialize_pinit(model.nr_states, threshold)

        # The penalty parameter for constraint violation
        self._mu = options.mu
        # Select which loop to start.
        if options.incremental:
            return self._incremental_loop(model, threshold, direction, options)
        return self._naive_loop(model, threshold, direction, options)

    def _naive_loop(self, model, threshold, dir, options):
        numstate = model.nr_states
        initstate = int(model.initial_states[0])
        for i in range(options.maxiter):
            self.iterations = i
            encoding_start = time.time()

            self._create_encoding(model, options, self._lower_state_bounds, self._upper_state_bounds)

            if dir == "above":
                self._encoding.addConstr(self._pVars[initstate] >= threshold)
            else:
                self._encoding.addConstr(self._pVars[initstate] <= threshold)
            self._set_objective(model, initstate, dir, options)
            self._violation_constraints(model, options)
            self._wdconstraints(model, options)

            self._pexpr = dict([[p.id, -0.5 * (
                self._paraminit[p.id]) ** 2 - self._paraminit[p.id] * (self._paramVars[p.id] - self._paraminit[p.id])]
                                for p in self._parameters])

            self._modelconstraints(model, dir, options)
            # Constraint for initial state
            self.encoding_timer += time.time() - encoding_start
            self._solve_model()

            # Prints the maximum violation
            maxx = 0
            for state in range(numstate):
                val = self._tau[state].x
                if val > maxx:
                    maxx = val

            if not options.silent:
                print("Max vio :", maxx)
                print("p =", self._pVars[initstate].x)

            result, pvalues = self._mc(threshold, initstate, dir, options)
            if result is not None:
                return result

            # Breaks if the violation is small and prints number of iterations and total time
            if abs(maxx) < 1e-8 and not options.mc_termination_check and not options.intermediate_mc:
                param_values = dict([[id, param_var.x] for id, param_var in self._paramVars.items()])
                return QcqpResult(self._pVars[initstate].x, param_values)
            # Updates the probability values for next iteration
            self._update_pinit(pvalues)

            # Updates the parameter values for next iteration
            for param_id, param_var in self._paramVars.items():
                if not isinstance(param_var, int):
                    if abs(param_var.x) > 1e-8:
                        self._paraminit[param_id] = param_var.x
                    else:
                        self._paraminit[param_id] = 0
            # Updates penalty parameter
            self._mu *= (max(self._pinit) + 1)
            if self._mu > 1e8:
                self._mu = 1e8

    def _incremental_loop(self, model, threshold, dir, options):
        numstate = model.nr_states
        initstate = int(model.initial_states[0])
        encoding_start = time.time()
        self._create_encoding(model, options, self._lower_state_bounds, self._upper_state_bounds)
        # Constraint for initial state
        if dir == "above":
            self._encoding.addConstr(self._pVars[initstate] >= threshold)
        else:
            self._encoding.addConstr(self._pVars[initstate] <= threshold)
        self._wdconstraints(model, options)
        self._violation_constraints(model, options)

        self.encoding_timer += time.time() - encoding_start

        only_quadratic = False
        for i in range(options.maxiter):
            self.iterations = i
            encoding_start = time.time()
            self._set_objective(model, initstate, dir, options)

            self._pexpr = dict([[p.id, -0.5 * (
                self._paraminit[p.id]) ** 2 - self._paraminit[p.id] * (self._paramVars[p.id] - self._paraminit[p.id])]
                                for p in self._parameters])
            if i == 0:
                if options.store_quadratic:
                    self._modelconstraints_store(model, dir, options)
                else:
                    self._modelconstraints(model, dir, options, only_quadratic)
            else:
                self._modelconstraints(model, dir, options, only_quadratic)

            self.encoding_timer += time.time() - encoding_start

            self._solve_model()

            result, pvalues = self._mc(threshold, initstate, dir, options)
            if result is not None:
                return result
            # Prints the maximum violation
            maxx = 0
            for state in range(numstate):
                val = self._tau[state].x
                if val > maxx:
                    maxx = val

            if not options.silent:
                print("Max vio :", maxx)
                print("p =", self._pVars[initstate].x)

            # Breaks if the violation is small and prints number of iterations and total time
            if abs(maxx) < 1e-8 and not options.mc_termination_check and not options.intermediate_mc:
                param_values = dict([[id, param_var.x] for id, param_var in self._paramVars.items()])
                return QcqpResult(self._pVars[initstate].x, param_values)
            # Updates the probability values for next iteration
            self._update_pinit(pvalues)


            # Updates the parameter values for next iteration
            for param_id, param_var in self._paramVars.items():
                if not isinstance(param_var, int):
                    if abs(param_var.x) > 1e-8:
                        #  print pVar
                        self._paraminit[param_id] = param_var.x
                    else:
                        self._paraminit[param_id] = 0
            # Updates penalty parameter
            self._mu *= (max(self._pinit) + 1)
            if self._mu > 1e8:
                self._mu = 1e8

            self._encoding.remove(self._encoding.getQConstrs())
            self._encoding.update()
            only_quadratic = True


class QcqpModelRepairStats():
    def __init__(self):
        pass

class QcqpModelRepair():

    def __init__(self, model_explorer):
        self._model_explorer = model_explorer
        self._model = None
        self._qcqp_options = None
        self._parameters = None
        self._threshold = None
        self._prob0 = None
        self._prob1 = None
        self._property_type = None
        self._reward_name = None
        self._solver = None
        self._incremental = False

    @property
    def solver_time(self):
        return self._solver.solver_timer

    @property
    def encoding_timer(self):
        return self._solver.encoding_timer

    @property
    def iterations(self):
        return self._solver.iterations + 1

    def initialize(self, problem_description, epsilon, incremental=True, all_welldefined=False,
                   store_quadratic = True, use_mc = "result_only", handle_violation="minimisation", fixed_threshold=True, verbose=False):
        if use_mc not in ["no", "result_only", "full"]:
            raise ValueError("Invalid argument for use_mc")
        if handle_violation not in ["minimisation", "constrained"]:
            raise ValueError("Invalid argument for handle_violation")
        if not fixed_threshold:
            raise RuntimeError("Only fixed thresholds are supported right now")
        if problem_description.property.operator == OperatorType.reward:
            self._property_type = "reward"
            self._reward_name = problem_description.property.reward_name
        elif problem_description.property.operator == OperatorType.probability:
            self._property_type = "probability"

        self._model = self._model_explorer.get_model()
        self._qcqp_options = QcqpOptions(mu=0.05, maxiter=1000000, graph_epsilon=epsilon, silent=not verbose, incremental=incremental, all_welldefined=all_welldefined,
                                         store_quadratic=store_quadratic, mc_termination_check=(use_mc == "result_only"), intermediate_mc=(use_mc == "full"),
                                         minimise_violation=(handle_violation=="minimisation")
                                         )
        self._parameters = problem_description.parameters
        variables = self._model.collect_probability_parameters()
        if self._property_type == "reward":
            variables.update(self._model.collect_reward_parameters())
        self._variables = dict([[v,self._parameters.get_parameter(v.name).interval] for v in variables])
        self._threshold = problem_description.threshold
        if self._property_type == "probability":
            (self._prob0, self._prob1) = self._model_explorer.prob01_states()
        elif self._property_type == "reward":
            (self._prob0, self._prob1) = self._model_explorer.rew0_states(), None

    def _evaluate_result(self, param_values):
        parameter_assignments = dict([[x, param_values[x.id]] for x in self._variables])
        sample = ParameterInstantiation()
        for x, val in parameter_assignments.items():
            sample[x] = pc.Rational(val)
        return sample, self._model_explorer.perform_sampling([sample])


    def _mc_check(self, param_values):
        parameter_assignments = dict([[x, param_values[x.id]] for x in self._variables])
        sample = ParameterInstantiation()
        for x, val in parameter_assignments.items():
            sample[x] = pc.Rational(val)
        return self._model_explorer.mc_single_point(sample)


    def run(self, direction, lower_state_var_bounds = None, upper_state_var_bounds = None):
        assert direction in ["above", "below"]
        self._solver = QcqpSolver(self._evaluate_result,  self._mc_check)

        result = self._solver.run(self._model, self._variables, self._prob0, self._prob1, float(self._threshold), direction,
                                  self._qcqp_options, self._property_type, self._reward_name,
                                   lower_state_var_bounds, upper_state_var_bounds)
        sample, mc_res = self._evaluate_result(result.parameter_values)
        print("Qcqp: {}: Mc: {}".format(result.value_at_initial, float(mc_res[sample])))
        print("iterations ={}".format(self._solver.iterations))
        print("solver time={}".format(self._solver.solver_timer))
        print("encoding time={}".format(self._solver.encoding_timer))

        print("iterate time={}".format(self._solver.iterate_timer))
        print("inner part = {}s ({})".format(self._solver._auxtimer1, self._solver._auxtimer1/self._solver._auxtimer2))
        print("adding constraints = {}s".format(self._solver._auxtimer3))
        return InstantiationResult(sample, mc_res[sample])


