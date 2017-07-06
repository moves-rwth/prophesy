import pycarl
import pycarl.gmp
import pycarl.gmp.formula

from pycarl._config import CARL_PARSER
if CARL_PARSER:
    import pycarl.parse
    import pycarl.gmp.parse


Variable = pycarl.Variable
VariableType = pycarl.VariableType
Integer = pycarl.gmp.Integer
Rational = pycarl.gmp.Rational
Monomial = pycarl.Monomial
Polynomial = pycarl.gmp.Polynomial
RationalFunction = pycarl.gmp.RationalFunction

SimpleConstraint = pycarl.gmp.formula.SimpleConstraintRatFunc
Constraint = pycarl.gmp.formula.Constraint
Relation = pycarl.formula.Relation
Formula = pycarl.gmp.formula.Formula

numerator = pycarl.gmp.numerator
denominator = pycarl.gmp.denominator


def parse(input):
    if not CARL_PARSER:
        raise ImportError("Parsing capabalities not available as pycarl was built without.")
    res = pycarl.parse.deserialize(input, pycarl.gmp);
