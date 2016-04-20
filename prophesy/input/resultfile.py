import re
from prophesy.data.rationalfunction import RationalFunction
from prophesy.data import interval
from prophesy.data.parameter import ParameterOrder, Parameter
from pycarl.core import Rational, Variable
from prophesy.data.constraint import parse_constraint
from pycarl.formula.formula import Constraint, Relation
from pycarl.parse import parseExpr

class ParametricResult(object):
    """Stores the data that may result from loading a parametric model, which
    are its parameters, the rationalfunction it describes and any constraints
    that apply to the parameters."""
    def __init__(self, parameters, parameter_constraints, ratfunc):
        """
        @param parameters ParameterOrder
        @param parameter_constraints List of constraints (pycarl.Formula or pycarl.Constraint)
        @param ratfunc pycarl.RationalFunction (or lower)
        """
        self.parameters = parameters
        self.parameter_constraints = parameter_constraints
        self.ratfunc = ratfunc

    def __str__(self):
        output_template = "Parameters: {params}\nParameter Constraints:\n    {constrs}\nResult: {results}\n"
        return output_template.format(params=", ".join(map(str, self.parameters)),
                                      constrs="\n    ".join(map(str, self.parameter_constraints)),
                                      results=self.ratfunc)


def read_pstorm_result(location):
    """Read the output of pstorm into a ParametricResult
    """
    with open(location) as f:
        inputstring = f.read()

    # Build parameters
    #print("Reading parameters...")
    parameters = ParameterOrder()
    parameter_strings = re.findall('!Parameters:\s(.*)', inputstring)[0].split(",")
    for parameter_string in parameter_strings:
        if parameter_string.strip():
            name_and_info = parameter_string.split()
            var = Variable(name_and_info[0].strip())
            if len(name_and_info) == 1:
                bound = interval.Interval(0.0, interval.BoundType.open,
                    1.0, interval.BoundType.open)
            else:
                bound = interval.string_to_interval(name_and_info[1], Rational)
            parameters.append(Parameter(var, bound))

    # Build well-defined constraints
    #print("Reading constraints...")
    constraints_string = re.findall(r'(!Well-formed Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)[0]
    constraints_string = constraints_string.split("\n")[:-1]
    constraints = [parse_constraint(cond) for cond in constraints_string[1:]]

    # Build graph-preserving constraints
    constraints_string = re.findall(r'(!Graph-preserving Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)
    if len(constraints_string) > 0:
        constraints_string = constraints_string[0].split("\n")[:-1]
    else:
        constraints_string = []
    gpconstraints = [parse_constraint(cond) for cond in constraints_string[1:]]
    constraints += gpconstraints

    # Build rational function
    #print("Reading rational function...")
    match = re.findall('!Result:(.*)$', inputstring, re.MULTILINE)[0]
    #print("Building rational function...")
    ratfunc = RationalFunction(parseExpr(match))

    #print("Parsing complete")
    return ParametricResult(parameters, constraints, ratfunc)


def write_pstorm_result(location, result):
    with open(location, "w") as f:
        f.write("!Parameters: {0}\n".format(", ".join([str(p) for p in vars])))
        f.write("!Result: {0}\n".format(str(result.result_function)))
        f.write("!Well-formed Constraints:\n{0}\n".format("\n".join([str(c) for c in result.parameter_constraints])))
        #f.write("!Graph-preserving Constraints:\n{0}\n".format("\n".join([str(c) for c in result.parameter_constraints])))

def read_param_result(location):
    with open(location) as f:
        inputs = [l.strip() for l in f.readlines()]

    # Build parameters
    #print("Reading parameters")
    parameters = ParameterOrder()
    parameter_strings = inputs[1][1:-1].split(", ")
    for parameter_string in parameter_strings:
        if parameter_string.strip():
            var = Variable(parameter_string.strip().strip())
            bound = interval.Interval(0.0, interval.BoundType.open,
                1.0, interval.BoundType.open)
            parameters.append(Parameter(var, bound))

    #print("Reading constraints")
    ranges = re.split(r"(?<=]) (?=\[)", inputs[2][1:-1])
    ranges = [r[1:-1].split(", ") for r in ranges]
    #print(ranges)
    if len(parameter_strings) != len(ranges):
        raise RuntimeError("Number of ranges does not match number of parameters")
    # Build well-defined constraints
    constraints = []
    for (p, ran) in zip(parameters, ranges):
        # ran = [lower .. upper]
        constraints.append(Constraint(p.variable - ran[0], Relation.GEQ))
        constraints.append(Constraint(p.variable - ran[1], Relation.LEQ))
    #print(constraints)

    # Build rational function
    #print("Parsing rational function")
    ratfunc = RationalFunction(parseExpr(inputs[3]))

    return ParametricResult(parameters, constraints, ratfunc)
