from sympy.polys import Poly
from sympy import Rational, Integer, Float


def print_term(term, variables):
    """Prints ((v1=2,v2=3),c1) as (* c v1 v1  v2 v2 v2)"""
    assert term[1] != 0
    factors = []
    if term[1] != 1 or sum(term[0]) == 0:
        factors.append(strNum(term[1]))

    for var, power in zip(variables, term[0]):
        # repeat var power times
        factors += [str(var)] * power

    poly_str = " ".join(factors)
    if len(factors) > 1:
        poly_str = "(* " + poly_str + ")"
    return poly_str


def print_terms(terms, variables):
    """Prints [t, t, t] as (+ t t t)"""
    poly_str = " ".join([print_term(term, variables) for term in terms])
    if len(terms) > 1:
        poly_str = "(+ " + poly_str + ")"
    else:
        pass
    return poly_str


def smt2strPoly(p, variables):
    """Returns a string representation of the Poly p in prefix notation."""
    assert isinstance(p, Poly)
    poly_str = print_terms(p.terms(), variables)
    return poly_str


def strNum(n):
    assert isinstance(n, Rational) or isinstance(n, Integer) or isinstance(n, Float)
    if isinstance(n, Float):
        n = Rational(n)
    num_str = ""
    if n.is_integer:
        if n >= 0:
            num_str = str(n)
        else:
            num_str = "(- " + str(abs(n)) + ")"
    else:
        (nom, den) = n.as_numer_denom()
        # Convert to Integer first, to avoid printing float representation
        assert den > 0
        if n >= 0:
            num_str = str(nom)
        else:
            num_str = "(- " + str(abs(nom)) + ") "
        if den != 1:
            num_str = "(/ " + num_str + " " + str(abs(den)) + ")"
    return num_str
