import pycarl
import pycarl.gmp
import pycarl.gmp.formula
import pycarl.formula
import pycarl.convert
import logging

from prophesy.config import modules

pycarl_parser_available = modules.has_pycarl_parser()

if pycarl_parser_available:
    if not pycarl.has_parser():
        raise RuntimeError("Pycarl parser is configured to be available, but could not be loaded")
    import pycarl.parse
    import pycarl.gmp.parse

    ParserError = pycarl.parse.ParserError
else:
    if pycarl.has_parser():
        logging.warning("Pycarl has a parser, but this is switched off")

    ParserError = RuntimeError

if pycarl.has_cln():
    import pycarl.cln
    import pycarl.cln.formula
    if pycarl_parser_available:
        import pycarl.cln.parse

# Set standard number type of pycarl (gmp or cln)
pycarl.numtype = pycarl.gmp

Variable = pycarl.Variable
VariableType = pycarl.VariableType
Integer = pycarl.numtype.Integer
Rational = pycarl.numtype.Rational
Monomial = pycarl.Monomial
Polynomial = pycarl.numtype.Polynomial
RationalFunction = pycarl.numtype.RationalFunction

SimpleConstraint = pycarl.numtype.formula.SimpleConstraintRatFunc
Constraint = pycarl.numtype.formula.Constraint
Relation = pycarl.formula.Relation
Formula = pycarl.numtype.formula.Formula

numerator = pycarl.numtype.numerator
denominator = pycarl.numtype.denominator
expand = pycarl.numtype.expand
variable_with_name = pycarl.variable_with_name

FormulaType = pycarl.formula.FormulaType

inf = pycarl.inf


def parse(input):
    if not pycarl.has_parser():
        raise ImportError("Parsing capabilities not available as pycarl was built without parsing support.")
    if not pycarl_parser_available:
        raise ImportError("Pycarl parsing capabilities are not configured.")

    return pycarl.parse.deserialize(input, pycarl.numtype)


if pycarl.numtype == pycarl.gmp:
    def convert_to_storm_type(data):
        assert pycarl.has_cln()
        return pycarl.convert.convert_to_cln(data)


    def convert_from_storm_type(data):
        return pycarl.convert.convert_to_gmp(data)

    def expand_from_storm_type(data):
        return pycarl.convert.convert_to_gmp(pycarl.cln.expand(data))

else:
    def convert_to_storm_type(data):
        return data

    def convert_from_storm_type(data):
        return pycarl.convert.convert_to_cln(data)


    def expand_from_storm_type(data):
        return pycarl.cln.expand(data)


