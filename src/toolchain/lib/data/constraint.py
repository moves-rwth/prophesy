#
# -*- coding: utf-8 -*-
from sympy.polys.polytools import Poly
from smt.polynomial_to_smt2 import smt2strPoly
import sympy

##################################################################################################
# Class representing a polynomial constraint.
# @author: Ulrich Loup
# @since: 2010-09-24
# @version: 2014-03-12
##################################################################################################

class Constraint:
    """Represents a polynomial constraint pol rel 0.
         @param pol polynomials (Poly)
         @param rel (str)
         @param syms main variables of this constraint (list<Symbol>)
    """
    RELATIONS = ["<", ">", "=", ">=", "<=", "<>"]  # the relations have to be ordered by size since otherwise parsing constraints would fail

    def __init__(self, pol, rel, syms):
        assert isinstance(pol, Poly)
        assert isinstance(syms, list)
        assert self.RELATIONS.__contains__(rel)
        self.polynomial = pol
        self.relation = rel
        self.symbols = syms

    @classmethod
    def __from_str__(cls, string, symbols):
        assert isinstance(string, str)
        assert isinstance(symbols, set) or isinstance(symbols, list)
        symbols = list(symbols)
        # Sort in reverse order of length, matching longest symbol first
        rels = sorted(Constraint.RELATIONS, key=len, reverse=True)
        for rel in rels:
            tokens = string.split(rel)
            if len(tokens) == 2:
                return cls(Poly(tokens[0] + "-" + tokens[1], symbols), rel, symbols)

    def __eq__(self, other):
        if not isinstance(other, Constraint): return False
        return str(self) == str(other)

    def __str__(self):
        return str(self.polynomial)[5:].split(",")[0] + " " + self.relation + " 0"

    def __repr__(self):
        return str(self.polynomial) + " " + self.relation + " 0"

    def __hash__(self):  # exclude identical constraints
        return hash(str(self))

    def to_smt2_string(self):
            return "(" + self.relation + " " + smt2strPoly(self.polynomial, self.symbols) + " 0)"

    def subs(self, substitutions):
        """ Performs the given list of substitutions on the polynomial of the constraint and
        adds all variables given by the substitutions to the new constraint. """
        self.symbols += [substitution[0] for substitution in substitutions if not substitution[0] in self.symbols]
        constraint = Constraint(self.polynomial.subs(substitutions), self.relation, self.symbols)
        return constraint

    def switch_variable_names(self, new_symbol_names):
        """ Switches the names of the current variables by the names given,
        where new_symbol_names needs to have the same length as the current list of variables. """
        assert len(new_symbol_names) == len(self.symbols)
        new_symbols = sympy.symbols(new_symbol_names)
        switch_list = zip(self.symbols, new_symbols)
        self.symbols = new_symbols
        self.polynomial = Poly(self.polynomial.subs(switch_list, simultaneous=True), self.symbols)
        return self

