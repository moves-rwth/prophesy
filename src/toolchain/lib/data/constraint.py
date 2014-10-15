#
# -*- coding: utf-8 -*-

from sympy import Symbol
from sympy import Rational, Integer, Float
from sympy.polys import Poly
from data.polynomial_to_smt2 import *

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
  RELATIONS = ["<",">","=",">=","<=","<>"] # the relations have to be ordered by size since otherwise parsing constraints would fail

  def __init__(self, pol, rel, syms):
    assert isinstance(pol, Poly) and isinstance(syms, list) and self.RELATIONS.__contains__(rel)
    self.polynomial = pol
    self.relation = rel
    self.symbols = syms
  
  @classmethod
  def __from_str__(cls, string, variables):
    assert isinstance(string, str)
    assert isinstance(variables, set) or isinstance(variables, list)
    variables = list(variables)
    relations1 = [ rel for rel in Constraint.RELATIONS if rel.__len__() == 1 ]
    relations2 = [ rel for rel in Constraint.RELATIONS if rel.__len__() == 2 ]
    tokens = []
    for rel in relations2: # first try the longer relations to not distort the splits by relations1
      tokens = string.split(rel)
      if tokens.__len__() == 2:
        return cls(Poly( tokens[0] + "-" + tokens[1], variables ), rel, variables)
    for rel in relations1:
      tokens = string.split(rel)
      if tokens.__len__() == 2:
        return cls(Poly( tokens[0] + "-" + tokens[1], variables ), rel, variables)
  
  def __eq__(self, other):
    if not isinstance(other, Constraint): return False
    return self.__str__().__eq__(other.__str__())
  
  def __str__(self):
    return str(self.polynomial)[5:].split(",")[0] + " " + self.relation + " 0"
  
  def __repr__(self):
    return str(self.polynomial) + " " + self.relation + " 0"
  
  def __hash__(self): # exclude identical constraints
    return self.__str__().__hash__()
  
  def to_smt2_string(self):
      return "(" + self.relation + " " + smt2strPoly(self.polynomial, self.symbols)  + " 0)"
  
  def subs(self, substitutions):
    """ Performs the given list of substitutions on the polynomial of the constraint and adds all variables given by the substitutions to the new constraint. """
    for substitution in substitutions:
      if not self.symbols.__contains__(substitution[0]):
        self.symbols += [substitution[0]]
    constraint = Constraint(self.polynomial.subs(substitutions), self.relation, self.symbols)
    return constraint
  
  def switchVariableNames(self, new_symbol_names):
    """ Switches the names of the current variables by the names given, where new_symbol_names needs to have the same length as the current list of variables. """
    assert new_symbol_names.__len__() == self.symbols.__len__()
    for i in range(self.symbols.__len__()):
      v = Symbol(new_symbol_names[i])
      x = self.symbols[i]
      self.symbols[i] = v
      self.polynomial = Poly(self.polynomial.subs([(x, v)]), self.symbols)
      assert isinstance(self.polynomial, Poly)
    return self
  
