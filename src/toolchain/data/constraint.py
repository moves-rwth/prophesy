#
# -*- coding: utf-8 -*-

from sympy import Symbol
from sympy import Rational, Integer, Float
from sympy.polys import Poly

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
    return "(" + self.relation + " " + strPoly(self.polynomial, self.symbols) + " 0" + ")"
  
  def __repr__(self):
    return self.__str__()
  
  def __hash__(self): # exclude identical constraints
    return self.__str__().__hash__()
  
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
  
def strPoly( p, variables ):
  """Returns a string representation of the Poly p in prefix notation."""
  assert isinstance(p, Poly) and isinstance(variables, list)
  poly_str = "(+"
  poly_close_str = ")"
  if p.terms().__len__() == 1:
    poly_str = ""
    poly_close_str = ""
  for term in p.terms():
    assert term[1] != 0
    closing = ""
    d = degree(term)
    if d > 1:
      poly_str += " (*"
      closing = ")"
      if term[1] != 1:
        poly_str += " " + strNum( term[1] )
    elif d == 1:
      if term[1] != 1:
        poly_str += " (*"
        closing = ")"
        poly_str += " " + strNum( term[1] )
    else:
      poly_str += " " + strNum( term[1] )
    i = 0
    for power in term[0]:
      assert i < variables.__len__()
      for e in range(power):
          poly_str += " " + variables[i].__str__()
      i = i + 1
    poly_str += closing
  poly_str += poly_close_str
  return poly_str

def strNum( n ):
  assert isinstance(n, Rational) or isinstance(n, Integer) or isinstance(n, Float)
  num_str = ""
  if n.is_integer:
    if n >= 0:
      num_str = n.__str__()
    else:
      num_str = "(- " + abs(n).__str__() + ")"
  else:
    if n >= 0:
      num_str = "(/ " + n.as_numer_denom()[0].__str__() + " " + n.as_numer_denom()[1].__str__() + ")"
    else:
      num_str = "(/ (- " + abs(n.as_numer_denom()[0]).__str__() + ") " + abs(n.as_numer_denom()[1]).__str__() + ")"
  return num_str
    
def degree(t):
  """ Returns the degree of the given term (as tuple ((exp_0, exp_1, ..., exp_k), coeff)."""
  assert isinstance(t, tuple)
  return sum(t[0])
