from abc import ABCMeta, abstractmethod
from enum import Enum

from prophesy.adapter.pycarl import Variable, VariableType, Rational, Polynomial
from prophesy.data.interval import Interval, BoundType
from prophesy.adapter.pycarl import Constraint, Relation

# Can we set the lower rat_func_bound to an open interval, thus exclude the zero?
def setup_smt(smt2interface, result, threshold, rat_func_bound = Interval(0, BoundType.closed, None, BoundType.open)):
    for p in result.parameters:
        smt2interface.add_variable(p.variable.name, VariableDomain.Real)

    for constr in result.parameter_constraints:
        print(result.parameter_constraints)
        smt2interface.assert_constraint(constr)

    rat_vars = result.parameters.get_variable_order()
    vars = rat_vars

    safeVar = Variable("__safe", VariableType.BOOL)
    badVar = Variable("__bad", VariableType.BOOL)
    thresholdVar = Variable("T")
    rf1Var = Variable("rf1")
    rf2Var = Variable("rf2")

    vars.append(safeVar)
    vars.append(badVar)
    vars.append(thresholdVar)
    vars.append(rf1Var)
    vars.append(rf2Var)

    smt2interface.add_variable(safeVar, VariableDomain.Bool)
    smt2interface.add_variable(badVar, VariableDomain.Bool)
    smt2interface.add_variable(thresholdVar, VariableDomain.Real)
    smt2interface.add_variable(rf1Var, VariableDomain.Real)
    smt2interface.add_variable(rf2Var, VariableDomain.Real)

    safe_relation = Relation.GEQ
    bad_relation = Relation.LESS

    safe_constraint = Constraint(rf1Var - thresholdVar * rf2Var, safe_relation)
    bad_constraint = Constraint(rf1Var - thresholdVar * rf2Var, bad_relation)
    #TODO: pycarl cannot deal with float everywhere, cast to rational
    threshold_constraint = Constraint(thresholdVar - threshold, Relation.EQ)

    rf1_constraint = Constraint(rf1Var - pycarl.numerator(result.ratfunc), Relation.EQ)
    rf2_constraint = Constraint(rf2Var - pycarl.denominator(result.ratfunc), Relation.EQ)
    smt2interface.assert_constraint(threshold_constraint)
    smt2interface.assert_constraint(rf1_constraint)
    smt2interface.assert_constraint(rf2_constraint)
    smt2interface.assert_guarded_constraint("__safe", safe_constraint)
    smt2interface.assert_guarded_constraint("__bad", bad_constraint)

    #TODO why do we only do this if the denominator is 1
    if pycarl.denominator(result.ratfunc) == Rational(1):
        if rat_func_bound.left_bound() != None:
            ineq_type = Relation.GEQ if rat_func_bound.left_bound_type() == BoundType.closed else Relation.GREATER
            lbound = Constraint(Polynomial(rf1Var), ineq_type)
            smt2interface.assert_constraint(lbound)
        if rat_func_bound.right_bound() != None:
            ineq_type = Relation.LEQ if rat_func_bound.left_bound_type() == BoundType.closed else Relation.LESS
            ubound = Constraint(Polynomial(rf1Var) - 1, ineq_type)
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
