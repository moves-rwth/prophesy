import tempfile

import re
import config
import subprocess
from sympy import Symbol
from sympy.polys import Poly
from data.constraint import Constraint
from data.rationalfunction import RationalFunction
from modelcheckers.ppmc import ParametricProbablisticModelChecker
from util import check_filepath_for_reading, run_tool, ensure_dir_exists

def parse_param_result_file(path):
    with open(path) as f:
        inputstring = f.read()
    inputs = inputstring.split("\n")
    print(inputstring)
    parameter_strings = inputs[1][1:-1].split(", ")
    print(parameter_strings)
    ranges = re.split(r"(?<=]) (?=\[)", inputs[2][1:-1])
    ranges = [r[1:-1].split(", ") for r in ranges]
    print(ranges)
    if len(parameter_strings) != len(ranges):
        raise RuntimeError("Number of ranges does not match number of parameters")
    pols = inputs[3].split(" / ")
    if len(pols) > 2:
        raise RuntimeError("Problems parsing param result file")

    parameters = [ Symbol(name.rstrip()) for name in parameter_strings ]

    wd_constraints = []
    for (p, ran) in zip(parameters, ranges):
        wd_constraints.append(Constraint(Poly(p, [p]) - Poly(ran[0], [p]), ">=", [p]))
        wd_constraints.append(Constraint(Poly(p, [p]) - Poly(ran[1], [p]), "<=", [p]))
    print(wd_constraints)

    nominator = Poly(pols[0], parameters)
    if len(pols) == 2:
        denominator = Poly(pols[1], parameters)
    else:
        denominator = Poly(1, parameters)
    return (parameters, wd_constraints, RationalFunction(nominator, denominator))


class ParamParametricModelChecker(ParametricProbablisticModelChecker):
    def __init__(self, location):
        self.location = location

    def name(self):
        return "param"

    def version(self):
        args = [self.location, "--help"]
        pipe = subprocess.Popen(args, stdout = subprocess.PIPE)
        # pipe.communicate()
        outputstr = pipe.communicate()[0].decode(encoding = 'UTF-8')
        output = outputstr.split("\n")
        return output[2][1:-1].strip()

    def get_rational_function(self, prism_file, pctl_filepath):
        check_filepath_for_reading(pctl_filepath, "pctl file")

        # create a temporary file for the result.
        ensure_dir_exists(config.CLI_INTERMEDIATE_FILES_DIR)
        resultfile = tempfile.mkstemp(suffix = ".txt", dir = config.CLI_INTERMEDIATE_FILES_DIR, text = True)

        args = [self.location,
                prism_file.location,
                pctl_filepath,
                "--result-file", resultfile[1],
                "--no-startup-message"]
        run_tool(args)

        print(resultfile[1])
        (params, wdconstraints, ratfunc) = parse_param_result_file(resultfile[1] + ".out")
        return (params, wdconstraints, [], ratfunc)




