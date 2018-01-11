from __future__ import division
import stormpy
import stormpy.core
import stormpy.logic
import stormpy.pars
import time
from prophesy.exceptions.unsupported_model import NotSupportedModel
from gurobipy import *



import prophesy.adapter.pycarl as pc
from prophesy.data.samples import ParameterInstantiation, InstantiationResult

class QcqpOptions():
    def __init__(self, mu, maxiter, graph_epsilon, silent):
        self.mu = mu
        self.maxiter = maxiter
        self.graph_epsilon = graph_epsilon
        self.silent = silent


class QcqpResult():
    def __init__(self, value_at_initial, parameter_values):
        self.value_at_initial = value_at_initial
        self.parameter_values = parameter_values


class QcqpSolver():
    def __init__(self):
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
        self._states_and_transitions = None

    def _check_prob0(self, state):
        return self._prob0E.get(state)

    def _check_prob1(self, state):
        return self._prob1A.get(state)

    def _compute_states_and_transitions(self, model):
        self._states_and_transitions = []
        for row_group in range(model.nr_states):
            self._states_and_transitions.append([])
            for row in range(model.transition_matrix.get_row_group_start(row_group),
                             model.transition_matrix.get_row_group_end(row_group)):
                for entry in model.transition_matrix.get_row(row):
                    self._states_and_transitions[-1].append((entry.value(), entry.column))

    def _solve_model(self):
        start3 = time.time()
        # Solves the problem
        print('Solving...')
        self._encoding.optimize()

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

    def _create_encoding(self, model, options):
        numstate = model.nr_states

        self._encoding = Model("qcp")
        self._encoding.setParam('OutputFlag', not options.silent)

        # Initializing some arrays for state, parameter and tau variables, and their values at previous iterations
        # Initializing gurobi variables for parameters,lb=lowerbound, ub=upperbound
        self._pVars = [self._encoding.addVar(lb=0, ub=1.0) for _ in range(numstate)]
        self._tau = [self._encoding.addVar(lb=0) for _ in range(numstate)]
        self._tt = self._encoding.addVar(lb=0.0, name="TT")
        self._paramVars = dict([[x.id, self._encoding.addVar(lb=options.graph_epsilon, ub=1-options.graph_epsilon)] for x in self._parameters])

        # Updates the model for gurobi
        self._encoding.update()

    def _float_repr(self, constant_val):
        v = self._constants_floats.get(constant_val, float(constant_val))
        self._constants_floats[constant_val] = v
        return v

    def _wdconstraints(self, model, options):

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
                                cons1 = cons1 + float(t.coeff) / float(den)
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

    def _modelconstraints(self, model, options, only_quadratic=False):
        numstate = model.nr_states

        for state in range(model.nr_states):
            #for act in range(model.transition_matrix.get_row_group_start(state),
            #             model.transition_matrix.get_row_group_end(state)):
            act = state
            # Cons=values constraints on the right hand side for a pdtmc
            cons = 0
            # A flag for linear vs quadratic constraints
            flag = 0

            for v,c in self._states_and_transitions[state]:
                t_cons, is_quadratic = self._modelconstraint_transition(state, (v,c), only_quadratic)
                if is_quadratic:
                    flag = 1
                cons += t_cons
            # If the constraint is quadratic, add a penalty term to the constraints, otherwise dont add the term
            if flag == 1:
                self._encoding.addQConstr(self._pVars[state] >= cons - self._tau[state])
            elif not only_quadratic:
                self._encoding.addConstr(self._pVars[state] >= cons)

    def _modelconstraint_transition(self, state, transition, only_quadratic=False):
        """
        
        :param state: 
        :param transition: 
        :return: 
        """
        t_cons = 0
        is_quadratic = False
        succ = int(transition[1])
        # Value of transition
        transition_value = transition[0]
        # TODO check that the denominator is indeed constant?

        if self._check_prob0(succ):
            return t_cons, is_quadratic

        proc_start = time.time()
        # If the transition value is not constant
        if not transition_value.is_constant():
            # Denominator of transition
            den = transition_value.denominator
            if den.is_one():
                denom1 = 1.0
            else:
                denom1 = 1 / self._float_repr(den.constant_part())
            num = self._numerator(transition_value)
            statevar = self._pVars[succ]

            # Iterates over terms in numerators
            for t in num:
                if t.is_one():
                    # Add just value of transition is the successor state is prob1 to the constraints
                    if self._check_prob1(succ):
                        t_cons += denom1
                    # Else add transitionvalue*p_succ to the constraint
                    else:
                        t_cons += denom1 * statevar
                # If the transition term is a constant
                elif t.is_constant():
                    # Add just value of transition is the successor state is prob1 to the constraints
                    if self._check_prob1(succ):
                        t_cons += self._float_repr(t.coeff) * denom1
                    # Else add transitionvalue*p_succ to the constraint
                    else:
                        t_cons += self._float_repr(t.coeff) * denom1 * statevar

                # If the transition term is not a constant
                else:
                    if t.tdeg > 1:
                        raise NotSupportedModel("We expect the term to be a single variable",
                                                str(transition_value))
                    param_id = t.monomial[0][0].id
                    if t.is_one():
                        coeff = 1.0
                    else:
                        coeff = self._float_repr(t.coeff)
                    # Adds transitionvalue*parameter_variable to the constraint if the successor is prob1

                    if self._check_prob1(succ):
                        t_cons += coeff * self._paramVars[param_id] * denom1
                    # Add the quadratic term to the constraints
                    else:
                        is_quadratic = True
                        check_t = time.time()
                        pinit_succ = self._pinit[succ]
                        paramvar = self._paramVars[param_id]
                        assert self._pexpr is not None
                        pexpr = self._pexpr[param_id]
                        coeff_times_denom = coeff * denom1
                        # The bilinear terms are split into convex+concave terms, then the concave term is underapproximated by a affine term
                        # First term in the addition is the affine term, second term is the convex term
                        if coeff < 0:
                            t_cons -= coeff_times_denom * (-0.5 * (pinit_succ) ** 2 - pinit_succ * (statevar - pinit_succ) + pexpr)
                            t_cons -= coeff_times_denom * 0.5 * (statevar - paramvar) * (statevar - paramvar)
                        else:
                            t_cons += coeff_times_denom * (-0.5 * (pinit_succ) ** 2 - pinit_succ * (statevar - pinit_succ) + pexpr)
                            t_cons += coeff_times_denom * 0.5 * (statevar + paramvar) * (statevar + paramvar)
                        self._auxtimer1 += time.time() - check_t
        # If the value of transition is constant
        else:
            # Get the value of transition
            constant_value = transition_value.constant_part()
            # If successor state is prob1, just add the value of transition
            if self._check_prob1(succ):
                t_cons = t_cons + self._float_repr(constant_value)
            # Else, add transitionvalue*p_succ
            else:
                t_cons = t_cons + self._float_repr(constant_value) * self._pVars[succ]
        self._auxtimer2 += time.time() - proc_start
        return t_cons, is_quadratic

    def _set_objective(self, model, initstate, options):
        numstate = model.nr_states
        # Adding terms to the objective
        objective = 0.0
        for state in range(numstate):
            # This constraints minimizes the max of violation
            self._encoding.addConstr(self._tau[state] <= self._tt)
            # This minimizes sum of violation, mu is the parameter that
            objective = objective + self._mu * self._tau[state]

        # Maximize the probability of initial state
        objective = objective - self._pVars[initstate]
        self._encoding.setObjective((objective), GRB.MINIMIZE)

    def run(self, model, parameters, prob0E, prob1A, threshold, direction, options):
        """
        Runs the QCQP procedure by a series of calls to gurobi.

        :param model: The model
        :type model: a stormpy dtmc/mdp
        :param parameters: The parameters occuring in the model
        :type parameters: a list of pycarl variables
        :param properties: The properties as an iterable over stormpy.properties
        :param threshold: The threshold
        :type threshold: float
        :param direction: Are we looking for a value below or above
        :type direction: a string, either "above" or "below"
        :param options: Further options with which the algorithm should run
        :return: 
        """
        assert direction in ["above", "below"]
        self._prob0E = prob0E
        self._prob1A = prob1A
        self._parameters = parameters
        if direction == "above":
            raise RuntimeError("Direction == above is currently not supported.")
        if not options.silent:
            print("Number of states: {}".format(model.nr_states))
            print("Number of transitions: {}".format(model.nr_transitions))
            print("Labels: {}".format(model.labeling.get_labels()))
            print(model.model_type)
            print("Number of states: {}".format(model.nr_states))


        numstate = model.nr_states
        # print(numstate)
        # Initializing some arrays for state, parameter and tau variables, and their values at previous iterations
        self._paraminit = dict([[x.id, 0.5] for x in parameters])
        self._pinit = [0.5 for _ in range(numstate)]

        # The penalty parameter for constraint violation
        self._mu = options.mu
        # Getting the initial state
        initstate = int(model.initial_states[0])
        for i in range(options.maxiter):
            self.iterations = i
            encoding_start = time.time()
            self._create_encoding(model, options)

            self._modelconstraints(model, options)
            #self._wdconstraints(model, options)
            ##Adds constraints for prob1 and prob0 state
            #self._prob01constraints(model)

            self._set_objective(model, initstate, options)
            # Constraint for initial state
            self._encoding.addConstr(self._pVars[initstate] <= threshold)
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

            # Breaks if the violation is small and prints number of iterations and total time
            if abs(maxx) < 1e-8:
                param_values = dict([[id, param_var.x] for id, param_var in self._paramVars.items()])
                return QcqpResult(self._pVars[initstate].x, param_values)
            # Updates the probability values for next iteration
            for state in range(numstate):
                if abs(self._pVars[state].x) > 1e-8:
                    self._pinit[state] = self._pVars[state].x
                else:
                    self._pinit[state] = 0

            # Updares the parameter values for next iteration
            for param_id, param_var in self._paramVars.items():
                if not isinstance(param_var, int):
                    if abs(param_var.x) > 1e-8:
                        #  print pVar
                        self._paraminit[param_id] = param_var.x
                    else:
                        self._paraminit[param_id] = 0
            # Updates penalty parameter
            self._mu *= 10.0

    def run_rm(self, model, parameters, prob0E, prob1A, threshold, direction, options):
        """
        Runs the QCQP procedure by a series of calls to gurobi.

        :param model: The model
        :type model: a stormpy dtmc/mdp
        :param parameters: The parameters occuring in the model
        :type parameters: a list of pycarl variables
        :param properties: The properties as an iterable over stormpy.properties
        :param threshold: The threshold
        :type threshold: float
        :param direction: Are we looking for a value below or above
        :type direction: a string, either "above" or "below"
        :param options: Further options with which the algorithm should run
        :return: 
        """
        assert direction in ["above", "below"]
        self._prob0E = prob0E
        self._prob1A = prob1A
        self._parameters = parameters
        self._compute_states_and_transitions(model)
        if direction == "above":
            raise RuntimeError("Direction == above is currently not supported.")
        if not options.silent:
            print("Number of states: {}".format(model.nr_states))
            print("Number of transitions: {}".format(model.nr_transitions))
            print("Labels: {}".format(model.labeling.get_labels()))
            print(model.model_type)
            print("Number of states: {}".format(model.nr_states))


        numstate = model.nr_states
        # print(numstate)
        # Initializing some arrays for state, parameter and tau variables, and their values at previous iterations
        self._paraminit = dict([[x.id, 0.5] for x in parameters])
        self._pinit = [0.5 for _ in range(numstate)]

        # The penalty parameter for constraint violation
        self._mu = options.mu
        # Getting the initial state
        initstate = int(model.initial_states[0])
        encoding_start = time.time()
        self._create_encoding(model, options)
        self._set_objective(model, initstate, options)
        # Constraint for initial state
        self._encoding.addConstr(self._pVars[initstate] <= threshold)
        self.encoding_timer += time.time() - encoding_start

        only_quadratic = False
        for i in range(options.maxiter):
            self.iterations = i
            encoding_start = time.time()
            self._pexpr = dict([[p.id, -0.5 * (
                                    self._paraminit[p.id]) ** 2 -self._paraminit[p.id] * (self._paramVars[p.id] - self._paraminit[p.id])] for p in self._parameters])
            self._modelconstraints(model, options, only_quadratic)
            #self._wdconstraints(model, options)
            ##Adds constraints for prob1 and prob0 state
            #self._prob01constraints(model)


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

            # Breaks if the violation is small and prints number of iterations and total time
            if abs(maxx) < 1e-8:
                param_values = dict([[id, param_var.x] for id, param_var in self._paramVars.items()])
                return QcqpResult(self._pVars[initstate].x, param_values)
            # Updates the probability values for next iteration
            for state in range(numstate):
                if abs(self._pVars[state].x) > 1e-8:
                    self._pinit[state] = self._pVars[state].x
                else:
                    self._pinit[state] = 0

            # Updares the parameter values for next iteration
            for param_id, param_var in self._paramVars.items():
                if not isinstance(param_var, int):
                    if abs(param_var.x) > 1e-8:
                        #  print pVar
                        self._paraminit[param_id] = param_var.x
                    else:
                        self._paraminit[param_id] = 0
            # Updates penalty parameter
            self._mu *= 10.0

            self._encoding.remove(self._encoding.getQConstrs())
            self._encoding.update()
            only_quadratic = True


def example_getting_started_06():
    #    path = stormpy.examples.files.prism_pdtmc_die
    # Model path and property
    # path = "/Users/sjunges/i2/freiburg_robots/Benchmarks/pmcs/prism_page_pmcs/repudiationK-2_standard.drn"
    path = "/Users/sjunges/Downloads/m2_pmcs/repudiationK-2_standard_m2.drn"

    print("Building model from {}".format(path))

    formula_str = "P=? [F \"unfair\"]"

    model = stormpy.build_parametric_model_from_drn(path)
    properties = stormpy.parse_properties(formula_str)
    threshold = 0.5
    direction = "below"  # can be "below" or "above"
    options = QcqpOptions(mu=0.05, maxiter=100, graph_epsilon=0.001, silent=False)

    parameters = model.collect_probability_parameters()

    prob0E, prob1A = stormpy.prob01max_states(model, properties[0].raw_formula.subformula)
    solver = QcqpSolver()
    result = solver.run(model, parameters, prob0E, prob1A, threshold, direction, options)
    parameter_assignments = dict([[x, result.parameter_values[x.id]] for x in parameters])
    print(parameter_assignments)
    instantiator = stormpy.pars.PDtmcInstantiator(model)

    # Check distance to result by storm (notice that also the point that storm checks slightly differs)
    rational_parameter_assignments = dict([[x, stormpy.RationalRF(val)] for x, val in parameter_assignments.items()])
    print(rational_parameter_assignments)
    instantiated_model = instantiator.instantiate(rational_parameter_assignments)
    mc_res = stormpy.model_checking(instantiated_model, properties[0]).at(model.initial_states[0])
    print("Qcqp: {}: Mc: {}".format(result.value_at_initial, mc_res))

    print("iternum={}".format(solver.iterations))
    print("solver time={}".format(solver.solver_timer))
    print("encoding time={}".format(solver.encoding_timer))
    print("iterate time={}".format(solver.iterate_timer))

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
        self._solver = None

    @property
    def solver_time(self):
        return self._solver.solver_timer

    @property
    def encoding_timer(self):
        return self._solver.encoding_timer

    @property
    def iterations(self):
        return self._solver.iterations

    def initialize(self, problem_description, epsilon, fixed_threshold=True):
        if not fixed_threshold:
            raise RuntimeError("Only fixed thresholds are supported right now")
        self._model = self._model_explorer.get_model()
        self._qcqp_options = QcqpOptions(mu=0.05, maxiter=100, graph_epsilon=epsilon, silent=True)
        self._parameters = problem_description.parameters
        self._variables = self._model.collect_probability_parameters()
        self._threshold = problem_description.threshold
        (self._prob0, self._prob1) = get_prob01States(self._model, self._model_explorer.pctlformula[0])


    def run(self, direction):
        assert direction in ["above", "below"]
        self._solver = QcqpSolver()
        result = self._solver.run_rm(self._model, self._variables, self._prob0, self._prob1, float(self._threshold), direction, self._qcqp_options)
        parameter_assignments = dict([[x, result.parameter_values[x.id]] for x in self._variables])
        sample = ParameterInstantiation()
        for x, val in parameter_assignments.items():
            sample[x] = pc.Rational(val)
        mc_res = self._model_explorer.perform_sampling([sample])
        print("Qcqp: {}: Mc: {}".format(result.value_at_initial, float(mc_res[sample])))
        print("iterations ={}".format(self._solver.iterations))
        print("solver time={}".format(self._solver.solver_timer))
        print("encoding time={}".format(self._solver.encoding_timer))

        print("iterate time={}".format(self._solver.iterate_timer))
        print("inner part = {}s ({})".format(self._solver._auxtimer1, self._solver._auxtimer1/self._solver._auxtimer2))
        return InstantiationResult(sample, mc_res[sample])


def get_prob01States(model, property):
    path_formula = property.raw_formula.subformula
    if type(path_formula) == stormpy.logic.EventuallyFormula:
        phi_formula = stormpy.logic.BooleanLiteralFormula(True)
        psi_formula = path_formula.subformula
    elif type(path_formula) == stormpy.logic.UntilFormula:
        phi_formula = path_formula.left_subformula
        psi_formula = path_formula.right_subformula
    else:
        raise ValueError("Property type not supported")
    phi_result = stormpy.model_checking(model, phi_formula)
    phi_states = phi_result.get_truth_values()
    psi_result = stormpy.model_checking(model, psi_formula)
    psi_states = psi_result.get_truth_values()
    (prob0, prob1) = stormpy.compute_prob01_states(model, phi_states, psi_states)
    return prob0, prob1
    # (prob0A, prob1E) = stormpy.compute_prob01max_states(model, phiStates, psiSta

