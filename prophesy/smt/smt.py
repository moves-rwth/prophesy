from abc import ABCMeta, abstractmethod
from enum import Enum
from sympy import Symbol, Poly
from data.interval import Interval, BoundType


# Can we set the lower rat_func_bound to an open interval, thus exclude the zero?
def setup_smt(smt2interface, result, threshold, rat_func_bound = Interval(0, BoundType.closed, None, BoundType.open)):
    from data.constraint import Constraint

    for p in result.parameters:
        smt2interface.add_variable(p[0].name, VariableDomain.Real)

    for constr in result.parameter_constraints:
        smt2interface.assert_constraint(constr)

    rat_vars = list([x[0] for x in result.parameters])
    vars = rat_vars

    safeVar = Symbol("safe")
    badVar = Symbol("bad")
    thresholdVar = Symbol("T")
    rf1Var = Symbol("rf1")
    rf2Var = Symbol("rf2")

    vars.append(safeVar)
    vars.append(badVar)
    vars.append(thresholdVar)
    vars.append(rf1Var)
    vars.append(rf2Var)

    print(vars)

    smt2interface.add_variable(safeVar, VariableDomain.Bool)
    smt2interface.add_variable(badVar, VariableDomain.Bool)
    smt2interface.add_variable(thresholdVar, VariableDomain.Real)
    smt2interface.add_variable(rf1Var, VariableDomain.Real)
    smt2interface.add_variable(rf2Var, VariableDomain.Real)

    safe_relation = ">="
    bad_relation = "<="



    safe_constraint = Constraint(Poly(rf1Var - thresholdVar * rf2Var, *vars), safe_relation, vars)
    print(safe_constraint)
    print(safe_constraint.to_smt2_string())
    bad_constraint = Constraint(Poly(rf1Var - thresholdVar * rf2Var, *vars, domain="RR"), bad_relation, vars)
    threshold_constraint = Constraint(Poly(thresholdVar - threshold, *vars), "=", vars)
    rf1_constraint = Constraint(Poly(rf1Var - result.ratfunc.nominator.as_expr(*rat_vars), *vars, domain="RR"), "=", vars)
    rf2_constraint = Constraint(Poly(rf2Var - result.ratfunc.denominator.as_expr(*rat_vars), *vars, domain="RR"), "=", vars)
    smt2interface.assert_constraint(threshold_constraint)
    smt2interface.assert_constraint(rf1_constraint)
    smt2interface.assert_constraint(rf2_constraint)
    smt2interface.assert_guarded_constraint("safe", safe_constraint)
    smt2interface.assert_guarded_constraint("bad", bad_constraint)

    #TODO why do we only do this if the denominator is 1
    if result.ratfunc.denominator == Poly(1, *rat_vars):
        if rat_func_bound.left_bound() != None:
            ineq_type = ">=" if rat_func_bound.left_bound_type() == BoundType.closed else ">"
            lbound = Constraint(Poly(rf1Var), ineq_type, vars)
            smt2interface.assert_constraint(lbound)
        if rat_func_bound.right_bound() != None:
            ineq_type = "<=" if rat_func_bound.left_bound_type() == BoundType.closed else "<"
            ubound = Constraint(Poly(rf1Var - 1), ineq_type, vars)
            smt2interface.assert_constraint(ubound)



class Answer(Enum):
    sat = 0
    unsat = 1
    unknown = 2
    killed = 3
    memout = 4
    timeout = 5


class VariableDomain(Enum):
    Bool = 0
    Real = 1
    Int = 2


class SMTSolver:
    __metaclass__ = ABCMeta

    @abstractmethod
    def name(self):
        raise NotImplementedError

    @abstractmethod
    def version(self):
        raise NotImplementedError

    @abstractmethod
    def check(self):
        raise NotImplementedError

    @abstractmethod
    def push(self):
        raise NotImplementedError

    @abstractmethod
    def pop(self):
        raise NotImplementedError

    @abstractmethod
    def add_variable(self):
        raise NotImplementedError

    @abstractmethod
    def assert_constraint(self, c):
        raise NotImplementedError

    @abstractmethod
    def assert_guarded_constraint(self, c):
        raise NotImplementedError

    @abstractmethod
    def set_guard(self, g, v):
        raise NotImplementedError

    @abstractmethod
    def from_file(self, p):
        raise NotImplementedError

    @abstractmethod
    def to_file(self, p):
        raise NotImplementedError

    def __enter__(self):
        self.push()
        return self

    def __exit__(self, type, value, tb):
        self.pop()
