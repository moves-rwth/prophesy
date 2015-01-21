from sympy.polys import Poly
from sympy import Rational, Integer, Float

def print_term(term, variables):
    """Prints ((v1=2,v2=3),c1) as (* c v1 v1  v2 v2 v2)"""
    factors = []
    for var, power in zip(variables,term[0]):
        # repeat var power times
        factors += [str(var)] * power
    if term[1] > 1:
        factors += term[1]

    poly_str = " ".join(factors)
    if len(factors) > 1:
        poly_str = "(* " + poly_str + ")"
    return poly_str

def print_terms(terms, variables):
    """Prints [t, t, t] as (+ t t t)"""
    poly_str = " ".join(map(print_term, terms))
    if len(terms) > 1:
        poly_str = "(+ " + poly_str + ")"
    else:
        pass
    return poly_str

def smt2strPoly(p, variables):
    """Returns a string representation of the Poly p in prefix notation."""
    assert isinstance(p, Poly)
    print(variables)
    poly_str = print_terms(p.terms())
    return poly_str

def strNum(n):
    assert isinstance(n, Rational) or isinstance(n, Integer) or isinstance(n, Float)
    num_str = ""
    if n.is_integer:
        if n >= 0:
            num_str = str(n)
        else:
            num_str = "(- " + str(abs(n)) + ")"
    else:
        (nom, den) = n.as_numer_denom()
        if n >= 0:
            num_str = "(/ " + str(nom) + " " + str(den) + ")"
        else:
            num_str = "(/ (- " + abs(str(nom)) + ") " + abs(str(den)) + ")"
    return num_str
