import pycarl
import pycarl.gmp
import pycarl.gmp.formula
import pycarl.gmp.parse

Variable = pycarl.Variable
VariableType = pycarl.VariableType
Integer = pycarl.gmp.Integer
Rational = pycarl.gmp.Rational
Polynomial = pycarl.gmp.Polynomial
RationalFunction = pycarl.gmp.RationalFunction

Constraint = pycarl.gmp.formula.Constraint
Relation = pycarl.formula.Relation
Formula = pycarl.gmp.formula.Formula

def parse(input):
    return pycarl.gmp.parse.parse(input);