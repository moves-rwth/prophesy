import re
import logging

from prophesy.data import interval
from prophesy.data.parameter import ParameterOrder, Parameter
import prophesy.adapter.pycarl as pc

from prophesy.adapter.pycarl import Constraint, Relation


logger = logging.getLogger(__name__)


class ParametricResult:
    """
    Stores the data that represent a property of a parametric model, which
    are its parameters, the solution function for the property
    and any constraints that apply to the parameters.
    """
    def __init__(self, parameters, parameter_constraints, graph_preservation_constraints, ratfunc):
        """
        :param parameters: ParameterOrder
        :param parameter_constraints: Constraints that have to be fulfilled on the parameters in order to induce a well-defined model.
        :type parameter_constraints: List[pycarl.Formula]
        :param graph_preservation_constraints: Constraints that ensure that the graph-structure remains 
        :type graph_preservation_constraints: List[pycarl.Formula]
        :param ratfunc: Solution function
        :type ratfunc: pycarl.RationalFunction (or lower)
        """
        self.parameters = parameters
        self.welldefined_constraints = parameter_constraints
        self.graph_preservation_constraints = graph_preservation_constraints
        self.ratfunc = ratfunc

    def __str__(self):
        output_template = "Parameters: {params}\nParameter Constraints:\n    {constrs}\nResult: {results}\n"
        return output_template.format(params=", ".join(map(str, self.parameters)),
                                      constrs="\n    ".join(map(str, self.welldefined_constraints)),
                                      results=self.ratfunc)


def read_pstorm_result(location, require_result=True):
    """
    Read the output of pstorm into a ParametricResult
    :param location: The location of the file to be read
    :type location: str
    :param require_result: If true, parsing fails if no result is found
    :type require_result: Bool
    :return: The data obtained from the model.
    :rtype: ParametricResult
    """
    logging.debug("Open result file from storm...")
    with open(location) as f:
        inputstring = f.read()



    # Build parameters
    logger.debug("Reading parameters...")
    parameters = ParameterOrder()
    parameter_strings = re.findall(r'\$Parameters:\s(.*)', inputstring)[0].split(";")
    for parameter_string in parameter_strings:
        if parameter_string.strip():
            name_and_info = parameter_string.split()
            var = pc.variable_with_name(name_and_info[0].strip())
            if var.is_no_variable:
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
    constraints_string = re.findall(r'(\$Well-formed Constraints:\s*\n.+?)(?=\$|(?:\s*\Z))', inputstring, re.DOTALL)[0]
    constraints_string = constraints_string.split("\n")[:-1]
    constraints = [pc.parse(cond) for cond in constraints_string[1:]]
    logger.debug("Constraints: %s",  ",".join([str(c) for c in constraints]))
    # Build graph-preserving constraints
    constraints_string = re.findall(r'(\$Graph-preserving Constraints:\s*\n.+?)(?=\$|(?:\s*\Z))', inputstring, re.DOTALL)[0]
    constraints_string = constraints_string.split("\n")
    gpconstraints = [pc.parse(cond) for cond in constraints_string[1:] if cond.strip() != ""]
    logger.debug("GP Constraints: %s", ",".join([str(c) for c in gpconstraints]))

    # Build rational function
    logger.debug("Looking for solution function...")
    match = re.findall(r'\$Result:(.*)$', inputstring, re.MULTILINE)

    if require_result:
        if len(match) == 0:
            raise ValueError("Expected a result in the result file at {}".format(location))
    if len(match) > 0:
        logger.debug("Building solution function...")
        solution = pc.parse(match[0])
        if isinstance(solution, pc.Monomial):
            solution = pc.Polynomial(solution)
        logger.debug("Solution function is %s", solution)
    else:
        solution = None

    logger.debug("Parsing complete.")
    return ParametricResult(parameters, constraints, gpconstraints, solution)


def write_pstorm_result(location, result):
    logger.info("Write solution function and constraints to %s", location)
    with open(location, "w") as f:
        f.write("$Parameters: {0}\n".format("; ".join([str(p) for p in result.parameters])))
        f.write("$Result: {0}\n".format((result.ratfunc.to_smt2())))
        f.write("$Well-formed Constraints:\n{0}\n".format("\n".join([c.to_smt2() for c in result.welldefined_constraints])))
        f.write("$Graph-preserving Constraints:\n{0}\n".format("\n".join([c.to_smt2() for c in result.graph_preservation_constraints])))


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
