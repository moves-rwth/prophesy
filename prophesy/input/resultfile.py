import re
from sympy import Symbol, fraction
from sympy.polys import Poly
from data.constraint import Constraint
from data.rationalfunction import RationalFunction
import data.interval
from config import configuration
from exceptions.module_error import ModuleError

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
        output_template = "Parameters: {params}\nParameter Constraints:\n    {constrs}\nResult: {results}\n"
        return output_template.format(params=", ".join(map(str, self.parameters)),
                                      constrs="\n    ".join(map(str, self.parameter_constraints)),
                                      results=self.ratfunc)


def read_pstorm_result(location):
    with open(location) as f:
        inputstring = f.read()

    # Build parameters
    #print("Reading parameters...")
    parameters = []
    parameter_strings = re.findall('!Parameters:\s(.*)', inputstring)[0].split(";")
    for parameter_string in parameter_strings:
        if parameter_string.strip():
            name_and_info = parameter_string.split()
            if len(name_and_info) == 1:
                parameters.append(tuple([Symbol(name_and_info[0].strip()), data.interval.Interval(0.0, data.interval.BoundType.open, 1.0, data.interval.BoundType.open)]))
            else:
                parameters.append(tuple([Symbol(name_and_info[0].strip()), data.interval.string_to_interval(name_and_info[1], float)]))

    # Build well-defined constraints
    #print("Reading constraints...")
    symbols = [x[0] for x in parameters]
    constraints_string = re.findall(r'(!Well-formed Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)[0]
    constraints_string = constraints_string.split("\n")[:-1]
    constraints = [Constraint.__from_str__(cond, symbols) for cond in constraints_string[1:]]

    # Build graph-preserving constraints
    constraints_string = re.findall(r'(!Graph-preserving Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)
    if len(constraints_string) > 0:
        constraints_string = constraints_string[0].split("\n")[:-1]
    else:
        constraints_string = []
    gpconstraints = [Constraint.__from_str__(cond, symbols) for cond in constraints_string[1:]]
    constraints += gpconstraints

    # Build rational function
    #print("Reading rational function...")
    match = re.findall('!Result:(.*)$', inputstring, re.MULTILINE)[0]
    nom, den = fraction(match)
    nom = Poly(nom, symbols)
    den = Poly(den, symbols)

    #print("Building rational function...")
    nominator = Poly(nom, symbols)
    denominator = Poly(den, symbols)
    ratfunc = RationalFunction(nominator, denominator)

    #print("Parsing complete")
    return ParametricResult(parameters, constraints, ratfunc)


def write_pstorm_result(location, result):
    if False and configuration.is_module_available("pycarl") and configuration.is_module_available("stormpy"):
        # Use pycarl
        import pycarl.numbers
        import pycarl.core

        with open(location, "w") as f:
            str(result.result_function)
            vars = result.result_function.gather_variables()
            print("!Parameters: {0}\n".format("; ".join([str(p) for p in vars])))
            print("!Result: {0}\n".format(str(result.result_function)))
            print("")
            f.write("!Parameters: {0}\n".format(", ".join([str(p) for p in vars])))
            f.write("!Result: {0}\n".format(str(result.result_function)))
            f.write("!Well-formed Constraints:\n{0}\n".format("\n".join([str(c) for c in result.constraints_well_formed])))
            f.write("!Graph-preserving Constraints:\n{0}\n".format("\n".join([str(c) for c in result.constraints_graph_preserving])))
    else:
        with open(location, "w") as f:
            f.write("!Parameters: {0}\n".format("; ".join([p[0].name + " " + str(p[1]) for p in result.parameters])))
            f.write("!Result: {0}\n".format(str(result.ratfunc)))
            f.write("!Well-formed Constraints:\n{0}\n".format("\n".join([str(c) for c in result.parameter_constraints])))
            f.write("!Graph-preserving Constraints:\n")


def read_param_result(location):
    with open(location) as f:
        inputs = [l.strip() for l in f.readlines()]

    # Build parameters
    #print("Reading parameters")
    parameter_strings = inputs[1][1:-1].split(", ")
    parameters = [Symbol(name.rstrip()) for name in parameter_strings]
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
