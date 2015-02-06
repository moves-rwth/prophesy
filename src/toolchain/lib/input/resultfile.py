import re
from sympy import Symbol, fraction
from sympy.polys import Poly
from data.constraint import Constraint
from data.rationalfunction import RationalFunction

class ParametricResult(object):
    """Wraps the results of pstorm and param
    self.parameters: List of Symbol()
    self.parameter_constraints: List of Constraint()
    self.ratfunc: Instance of RationalFunction"""
    def __init__(self, params, parameter_constraints, ratfunc):
        self.parameters = params
        self.parameter_constraints = parameter_constraints
        self.ratfunc = ratfunc

    def __str__(self):
        return "Parameters: {0}\nParameter Constraints:\n    {1}\nResult: {2}\n".format(
                ", ".join(map(str, self.parameters)),
                "\n    ".join(map(str, self.parameter_constraints)),
                self.ratfunc
                )

def read_pstorm_result(location):
    with open(location) as f:
        inputstring = f.read()

    # Build parameters
    #print("Reading parameters...")
    parameter_strings = re.findall('!Parameters:\s(.*)', inputstring)[0].split(",")
    parameters = [ Symbol(name.strip()) for name in parameter_strings if name.strip() ]

    # Build well-defined constraints
    #print("Reading constraints...")
    constraintsString = re.findall(r'(!Well-formed Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)[0]
    constraintsString = constraintsString.split("\n")[:-1]
    constraints = [ Constraint.__from_str__(cond, parameters) for cond in constraintsString[1:] ]

    # Build graph-preserving constraints
    constraintsString = re.findall(r'(!Graph-preserving Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)
    if len(constraintsString) > 0:
        constraintsString = constraintsString[0].split("\n")[:-1]
    else:
        constraintsString = []
    gpconstraints = [ Constraint.__from_str__(cond, parameters) for cond in constraintsString[1:] ]
    constraints += gpconstraints

    # Build rational function
    #print("Reading rational function...")
    match = re.findall('!Result:(.*)$', inputstring, re.MULTILINE)[0]
    (nom,den) = fraction(match)
    nom = Poly(nom, parameters)
    den = Poly(den, parameters)

    #print("Building rational function...")
    nominator = Poly(nom, parameters)
    denominator = Poly(den, parameters)
    ratfunc = RationalFunction(nominator, denominator)

    #print("Parsing complete")
    return ParametricResult(parameters, constraints, ratfunc)

def write_pstorm_result(location, result):
    with open(location, "w") as f:
        f.write("!Parameters: {0}\n".format(", ".join([p.name for p in result.parameters])))
        f.write("!Result: {0}\n".format(str(result.ratfunc)))
        f.write("!Well-formed Constraints:\n{0}\n".format("\n".join([str(c) for c in result.parameter_constraints])))
        f.write("!Graph-preserving Constraints:\n")

def read_param_result(location):
    with open(location) as f:
        inputs = [l.strip() for l in f.readlines()]

    # Build parameters
    #print("Reading parameters")
    parameter_strings = inputs[1][1:-1].split(", ")
    parameters = [ Symbol(name.rstrip()) for name in parameter_strings ]
    #print(parameter_strings)

    #print("Reading constraints")
    ranges = re.split(r"(?<=]) (?=\[)", inputs[2][1:-1])
    ranges = [r[1:-1].split(", ") for r in ranges]
    #print(ranges)
    if len(parameter_strings) != len(ranges):
        raise RuntimeError("Number of ranges does not match number of parameters")
    # Build well-defined constraints
    wdconstraints = []
    for (p, ran) in zip(parameters, ranges):
        wdconstraints.append(Constraint(Poly(p, [p]) - Poly(ran[0], [p]), ">=", [p]))
        wdconstraints.append(Constraint(Poly(p, [p]) - Poly(ran[1], [p]), "<=", [p]))
    #print(wdconstraints)

    # Build rational function
    #print("Parsing rational function")
    (nom, den) = fraction(inputs[3])
    nominator = Poly(nom, parameters)
    denominator = Poly(den, parameters)
    ratfunc = RationalFunction(nominator, denominator)

    return ParametricResult(parameters, wdconstraints, ratfunc)
