#!/usr/bin/env python3

import os
import sys

# import library. Using this instead of appends prevents naming clashes..
this_file_path = os.path.dirname(os.path.realpath(__file__))
# insert at position 1; leave path[0] (directory at invocation) intact
sys.path.insert(1, os.path.join(this_file_path, '../prophesy'))

from argparse import ArgumentParser

from input.prismfile import PrismFile
from input.pctlfile import PctlFile
from input.resultfile import write_pstorm_result
from modelcheckers.param import ParamParametricModelChecker
from modelcheckers.storm import StormModelChecker

import config
from config import configuration

def parse_cli_args(pmcs):
    parser = ArgumentParser(description='Transform a prism file to a rational function.')

    parser.add_argument('--file', help='the input file containing the prism file', required=True)
    parser.add_argument('--pctl-file', help='a file with a pctl property', required=True)
    parser.add_argument('--pctl-index', help='the index for the pctl file', default=0)
    parser.add_argument('--result-file', help='resulting file', default="result.out")

<<<<<<< HEAD:src/toolchain/prophesy/cli/prismfiletoratfunc.py
    solver_group = parser.add_mutually_exclusive_group(required=True)
    solver_group.add_argument('--param', help='use param via cli')
    solver_group.add_argument('--storm', help='use storm via cli')
    solver_group.add_argument('--prism', help='use prism via cli')
    solver_group.add_argument('--stormpy', help='use the python API')
=======
    solver_group = parser.add_mutually_exclusive_group(required=not pmcs)
    solver_group.add_argument('--param', help='call the param tool')
    solver_group.add_argument('--storm', help='the location of the pstorm binary')
    solver_group.add_argument('--comics', help='the location of the comics binary')
>>>>>>> d16e32abe56a678081933919add331f52eaa46a9:src/toolchain/cli/prismfiletoratfunc.py

    return parser.parse_args()


if __name__ == "__main__":
    pmcs = configuration.getAvailableParametricMCs()
    cmdargs = parse_cli_args(pmcs)

    prism_file = PrismFile(cmdargs.file)
    pctl_file = PctlFile(cmdargs.pctl_file)

    if cmdargs.param is not None:
        prism_file.make_temporary_copy()
        prism_file.replace_parameter_keyword("param float")
        tool = ParamParametricModelChecker(cmdargs.param)
    elif cmdargs.storm is not None:
<<<<<<< HEAD:src/toolchain/prophesy/cli/prismfiletoratfunc.py
        tool = StormModelChecker(cmdargs.pstorm)
=======
        tool = StormModelChecker(cmdargs.storm)
    elif cmdargs.comics is not None:
        tool = ParamParametricModelChecker(vars(cmdargs)["param"])
    elif 'pstorm' in pmcs:
        tool = StormModelChecker(configuration.get(config.EXTERNAL_TOOLS, "storm"))
    elif 'param' in pmcs:
        tool = ParamParametricModelChecker(configuration.get(config.EXTERNAL_TOOLS, "param"))
>>>>>>> d16e32abe56a678081933919add331f52eaa46a9:src/toolchain/cli/prismfiletoratfunc.py
    else:
        raise RuntimeError("No supported model checker defined")

    print("Compute the rational function using " + tool.version())
    tool.load_model_from_prismfile(prism_file)
    tool.set_pctl_formula(pctl_file.get(cmdargs.pctl_index))
    result = tool.eliminate_states()
    write_pstorm_result(vars(cmdargs)["result_file"], result)

