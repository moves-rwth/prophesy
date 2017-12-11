import pycarl
import pycarl.gmp
import pycarl.gmp.formula
import pycarl.formula
import pycarl.convert

if pycarl.has_parser():
    import pycarl.parse
    import pycarl.gmp.parse

    ParserError = pycarl.parse.ParserError
else:
    ParserError = RuntimeError

if pycarl.has_cln():
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
expand = pycarl.gmp.expand
variable_with_name = pycarl.variable_with_name

FormulaType = pycarl.formula.FormulaType

inf = pycarl.inf


def parse(input):
    if not pycarl.has_parser():
        raise ImportError("Parsing capabilities not available as pycarl was built without parsing support.")
    return pycarl.parse.deserialize(input, pycarl.gmp)


if pycarl.has_cln():
    def convert_to_storm_type(data):
        return pycarl.convert.convert_to_cln(data)


    def convert_from_storm_type(data):
        return pycarl.convert.convert_to_gmp(data)
else:
    def convert_to_storm_type(data):
        return data


    def convert_from_storm_type(data):
        return data
