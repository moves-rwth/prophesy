import pycarl
import pycarl.gmp
import pycarl.gmp.formula
import pycarl.formula
import pycarl.convert

from pycarl._config import CARL_PARSER, CARL_WITH_CLN

if CARL_PARSER:
    import pycarl.parse
    import pycarl.gmp.parse

    ParserError = pycarl.parse.ParserError
else:
    ParserError = RuntimeError

if CARL_WITH_CLN:
    import pycarl.cln
    import pycarl.cln.formula

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

FormulaType = pycarl.formula.FormulaType


def parse(input):
    if not CARL_PARSER:
        raise ImportError("Parsing capabalities not available as pycarl was built without.")
    return pycarl.parse.deserialize(input, pycarl.gmp);


if CARL_WITH_CLN:
    def convert_to(data):
        return pycarl.convert.convert_to_cln(data)


    def convert_from(data):
        return pycarl.convert.convert_to_gmp(data)
else:
    def convert_to(data):
        return data


    def convert_from(data):
        return data
