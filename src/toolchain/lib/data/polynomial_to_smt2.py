from sympy.polys import Poly
from sympy import Symbol
from sympy import Rational, Integer, Float

def degree(t):
  """ Returns the degree of the given term (as tuple ((exp_0, exp_1, ..., exp_k), coeff)."""
  assert isinstance(t, tuple)
  return sum(t[0])
 

def smt2strPoly( p, variables ):
  """Returns a string representation of the Poly p in prefix notation."""
  assert isinstance(p, Poly)
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
    