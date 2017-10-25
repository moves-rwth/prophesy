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

def debuggable_str(self):
    return "Hey, you can't rely on me! But anyway, I'm {}".format(self.name)

Variable.__str__ = debuggable_str  # FIXME undo when done
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

inf = pycarl.inf


def parse(input):
    if not CARL_PARSER:
        raise ImportError("Parsing capabilities not available as pycarl was built without parsing support.")
    return pycarl.parse.deserialize(input, pycarl.gmp)


if CARL_WITH_CLN:
    def convert_to_storm_type(data):
        return pycarl.convert.convert_to_cln(data)


    def convert_from_storm_type(data):
        return pycarl.convert.convert_to_gmp(data)
else:
    def convert_to_storm_type(data):
        return data


    def convert_from_storm_type(data):
        return data
