import re
from sympy import Symbol
from sympy.polys import Poly
from data.constraint import Constraint
from data.rationalfunction import RationalFunction

class ParametricResult(object):
    """Wraps the results of pstorm and param
    self.parameters: List of Symbol()
    self.wdconstraints: List of Constraint()
    self.gpconstraint: List of Constraint()
    self.ratfunc: Instance of RationalFunction"""
    def __init__(self, params, wdconstraints, gpconstraints, ratfunc):
        self.parameters = params
        self.wdconstraints = wdconstraints
        self.gpconstraints = gpconstraints
        self.ratfunc = ratfunc

    def __str__(self):
        return "Parameters: {0}\nWell-formed Constraints:      {1}\nGraph-preserving Constraints: {2}\nResult: {3}\n".format(
                ", ".join(map(str, self.parameters)),
                "\n                             ".join(map(str, self.wdconstraints)),
                "\n                             ".join(map(str, self.gpconstraints)),
                self.ratfunc
                )

def _find_nominator(string):
    parenthesesCount = 0
    nominatorstring = ""
    for char in string:
        nominatorstring += char
        if char == "(":
            parenthesesCount += 1
        elif char == ")":
            if parenthesesCount == 0:
                raise RuntimeError("Unmatched closing parenthesis")
            parenthesesCount -= 1
            if parenthesesCount == 0:
                return nominatorstring

def read_pstorm_result(location):
    with open(location) as f:
        inputstring = f.read()
    # Build parameters
    print("Reading parameters...")
    parameter_strings = re.findall('!Parameters:\s(.*)', inputstring)[0].split(",")
    parameters = [ Symbol(name.strip()) for name in parameter_strings if name.strip() ]

    # Build well-defined constraints
    print("Reading constraints...")
    welldefined_constraintsString = re.findall(r'(!Well-formed Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)[0]
    welldefined_constraintsStrings = welldefined_constraintsString.split("\n")[:-1]
    wdconstraints = [ Constraint.__from_str__(cond, parameters) for cond in welldefined_constraintsStrings[1:] ]

    # Build graph-preserving constraints
    graphpreserving_constraintsStringList = re.findall(r'(!Graph-preserving Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)
    if len(graphpreserving_constraintsStringList) > 0:
        graphpreserving_constraintsStrings = graphpreserving_constraintsStringList[0].split("\n")[:-1]
    else:
        graphpreserving_constraintsStrings = []
    gpconstraints = [ Constraint.__from_str__(cond, parameters) for cond in graphpreserving_constraintsStrings[1:] ]

    # Build rational function
    print("Reading rational function...")
    match = re.findall('!Result:(.*)$', inputstring, re.MULTILINE)[0]
    resultingRatFunNom = _find_nominator(match)
    match = match[len(resultingRatFunNom):]
    # print("Denominator match {0}".format(match))
    if len(match) > 1:
        resultingRatFunDen = match.split("/")[1]

    print("Building rational function...")
    nominator = Poly(resultingRatFunNom, parameters)
    denominator = Poly(1, parameters)
    if resultingRatFunDen != None:
        denominator = Poly(resultingRatFunDen, parameters)
    ratfunc = RationalFunction(nominator, denominator)

    print("Parsing complete")
    return ParametricResult(parameters, wdconstraints, gpconstraints, ratfunc)

def write_pstorm_result(location, result):
    with open(location, "w") as f:
        f.write("!Parameters: {0}\n".format(", ".join([p.name for p in result.parameters])))
        f.write("!Result: {0}\n".format(str(result.ratfunc)))
        f.write("!Well-formed Constraints:\n{0}\n".format("\n".join([str(c) for c in result.wdconstraints])))
        f.write("!Graph-preserving Constraints:\n{0}".format("\n".join([str(c) for c in result.gpconstraints])))

def read_param_result(location):
    with open(location) as f:
        inputs = [l.strip() for l in f.readlines()]

    # Build parameters
    print("Reading parameters")
    parameter_strings = inputs[1][1:-1].split(", ")
    parameters = [ Symbol(name.rstrip()) for name in parameter_strings ]
    #print(parameter_strings)

    print("Reading constraints")
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

    print("Reading rational function")
    pols = inputs[3].split(" / ")
    if len(pols) > 2:
        raise RuntimeError("Problems parsing param result file")
    # Build rational function
    print("Parsing rational function")
    nominator = Poly(pols[0], parameters)
    if len(pols) == 2:
        denominator = Poly(pols[1], parameters)
    else:
        denominator = Poly(1, parameters)
    ratfunc = RationalFunction(nominator, denominator)

    return ParametricResult(parameters, wdconstraints, [], ratfunc)
