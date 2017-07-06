import re
import logging

from prophesy.data import interval
from prophesy.data.parameter import ParameterOrder, Parameter
import prophesy.adapter.pycarl as pc

from prophesy.adapter.pycarl import Constraint, Relation


logger = logging.getLogger(__name__)


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
    logger.debug("Reading parameters...")
    parameters = ParameterOrder()
    parameter_strings = re.findall('!Parameters:\s(.*)', inputstring)[0].split(";")
    for parameter_string in parameter_strings:
        if parameter_string.strip():
            name_and_info = parameter_string.split()
            var = pc.Variable(name_and_info[0].strip())
            if len(name_and_info) == 1:
                bound = interval.Interval(pc.Rational(0), interval.BoundType.open,
                    pc.Rational(1), interval.BoundType.open)
            else:
                bound = interval.string_to_interval(name_and_info[1], pc.Rational)
            parameters.append(Parameter(var, bound))
    logger.debug("Parameters: %s", str(parameters))

    # Build well-defined constraints
    logging.debug("Reading constraints...")
    constraints_string = re.findall(r'(!Well-formed Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)[0]
    constraints_string = constraints_string.split("\n")[:-1]
    constraints = []
    constraints = [pc.parse(cond) for cond in constraints_string[1:]]

    # Build graph-preserving constraints
    constraints_string = re.findall(r'(!Graph-preserving Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)
    if len(constraints_string) > 0:
        constraints_string = constraints_string[0].split("\n")[:-1]
    else:
        constraints_string = []
    gpconstraints = []
    gpconstraints = [pc.parse(cond) for cond in constraints_string[1:]]
    constraints += gpconstraints


    # Build rational function
    logger.debug("Reading rational function...")
    match = re.findall('!Result:(.*)$', inputstring, re.MULTILINE)[0]
    logger.debug("Building rational function...")
    solution = pc.parse(match)

    if isinstance(solution, pc.Monomial):
        solution = pc.Polynomial(solution)
    logger.debug("Rational function is %s", solution)

    logger.debug("Parsing complete.")
    return ParametricResult(parameters, constraints, solution)


def write_pstorm_result(location, result):
    logger.info("Write solution function and constraints to %s", location)
    with open(location, "w") as f:
        f.write("!Parameters: {0}\n".format("; ".join([str(p) for p in result.parameters])))
        f.write("!Result: {0}\n".format((result.ratfunc.to_smt2())))
        f.write("!Well-formed Constraints:\n{0}\n".format("\n".join([c.to_smt2() for c in result.parameter_constraints])))
        f.write("!Graph-preserving Constraints:\n{0}\n".format("\n".join([c.to_smt2() for c in result.parameter_constraints])))


def read_param_result(location):
    with open(location) as f:
        inputs = [l.strip() for l in f.readlines()]

    # Build parameters
    logger.debug("Reading parameters")
    parameters = ParameterOrder()
    parameter_strings = inputs[1][1:-1].split(", ")
    for parameter_string in parameter_strings:
        if parameter_string.strip():
            var = pc.Variable(parameter_string.strip().strip())
            bound = interval.Interval(0.0, interval.BoundType.open,
                1.0, interval.BoundType.open)
            parameters.append(Parameter(var, bound))

    logger.debug("Reading constraints")
    ranges = re.split(r"(?<=]) (?=\[)", inputs[2][1:-1])
    ranges = [r[1:-1].split(", ") for r in ranges]
    if len(parameter_strings) != len(ranges):
        raise RuntimeError("Number of ranges does not match number of parameters")
    # Build well-defined constraints
    constraints = []
    for (p, ran) in zip(parameters, ranges):
        # ran = [lower .. upper]
        constraints.append(Constraint(p.variable - ran[0], Relation.GEQ))
        constraints.append(Constraint(p.variable - ran[1], Relation.LEQ))

    # Build rational function
    logger.debug("Parsing rational function")
    ratfunc = pc.RationalFunction(parse(inputs[3]))

    return ParametricResult(parameters, constraints, ratfunc)
