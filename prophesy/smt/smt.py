from abc import ABCMeta, abstractmethod
from enum import Enum
import logging

import prophesy.adapter.pycarl as pc
from prophesy.data.interval import Interval, BoundType
from prophesy.adapter.pycarl import Constraint, Relation


# Can we set the lower rat_func_bound to an open interval, thus exclude the zero?
# TODO this method has to change, if we also support direct encoding of the lin eq system.
def setup_smt(smt2interface, result, threshold, rat_func_bound = Interval(0, BoundType.closed, None, BoundType.open)):
    for p in result.parameters:
        smt2interface.add_variable(p.variable.name, VariableDomain.Real)

    for constr in result.parameter_constraints:
        logging.debug(result.parameter_constraints)
        smt2interface.assert_constraint(constr)

    rat_vars = result.parameters.get_variables()
    vars = rat_vars

    safeVar = pc.Variable("__safe", pc.VariableType.BOOL)
    badVar = pc.Variable("__bad", pc.VariableType.BOOL)
    thresholdVar = pc.Variable("T")
    rf1Var = pc.Variable("rf1")
    rf2Var = pc.Variable("rf2")

    vars.append(safeVar)
    vars.append(badVar)
    vars.append(thresholdVar)
    vars.append(rf1Var)
    vars.append(rf2Var)

    smt2interface.add_variable(safeVar, VariableDomain.Bool)
    smt2interface.add_variable(badVar, VariableDomain.Bool)
    smt2interface.add_variable(thresholdVar, VariableDomain.Real)


    safe_relation = pc.Relation.GEQ
    bad_relation = pc.Relation.LESS

    if pc.denominator(result.ratfunc) != 1:
        smt2interface.add_variable(rf1Var, VariableDomain.Real)
        smt2interface.add_variable(rf2Var, VariableDomain.Real)
        safe_constraint = Constraint(pc.Polynomial(rf1Var) - thresholdVar * rf2Var, safe_relation)
        bad_constraint = Constraint(pc.Polynomial(rf1Var) - thresholdVar * rf2Var, bad_relation)
        rf1_constraint = Constraint(rf1Var - pc.numerator(result.ratfunc), Relation.EQ)
        rf2_constraint = Constraint(rf2Var - pc.denominator(result.ratfunc), Relation.EQ)
        smt2interface.assert_constraint(rf1_constraint)
        smt2interface.assert_constraint(rf2_constraint)
    else:
        safe_constraint = Constraint(pc.numerator(result.ratfunc) - thresholdVar, safe_relation)
        bad_constraint = Constraint(pc.numerator(result.ratfunc) - thresholdVar, bad_relation)


    threshold_constraint = Constraint(pc.Polynomial(thresholdVar) - threshold, Relation.EQ)

    smt2interface.assert_constraint(threshold_constraint)
    smt2interface.assert_guarded_constraint("__safe", safe_constraint)
    smt2interface.assert_guarded_constraint("__bad", bad_constraint)


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
