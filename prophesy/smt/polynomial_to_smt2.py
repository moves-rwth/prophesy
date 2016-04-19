from pycarl import Rational, Variable, Monomial, Term, Polynomial, \
    FactorizedPolynomial, RationalFunction, FactorizedRationalFunction, Formula

def ratfunc_to_smtlib(func):
    """Walks throughthe argument and returns it as SMTLib constraint
    @param func pycarl function object
    """
    if isinstance(func, (RationalFunction, FactorizedRationalFunction)):
        return "(/ {} {})".format(ratfunc_to_smtlib(func.nominator),
            ratfunc_to_smtlib(func.denominator))
    elif isinstance(func, (Polynomial, FactorizedPolynomial)):
        return "(+ {})".format(
            " ".join([ratfunc_to_smtlib(term) for term in func]))
    elif isinstance(func, Term):
        return "(* {} {})".format(ratfunc_to_smtlib(func.coeff),
            ratfunc_to_smtlib(func.monomial))
    elif isinstance(func, Monomial):
        result = ""
        for var, exp in func:
            result += " ".join([ratfunc_to_smtlib(var)] * exp)
        return "(* {})".format(" ".join(result))
    elif isinstance(func, Variable):
        return func.name
    elif isinstance(func, Rational):
        if func.nominator < 0:
            result = "(- {})".format(func.nominator)
        else:
            result = str(func.nominator)
        if func.denominator != 1:
            result = "(/ {} {})".format(result, func.denominator)
        return result
    else:
        assert False, "Unknown type to convert to SMTLib: " + repr(func)

def smt2strPoly(func):
    """Returns a string representation of the Poly func in SMTLib notation.
    @param func pycarl function object
    """
    return str(Formula(func))
    #return ratfunc_to_smtlib(func)
