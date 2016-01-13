#!/usr/bin/env python3

import os
import sys

# import library. Using this instead of appends prevents naming clashes..
this_file_path = os.path.dirname(os.path.realpath(__file__))
# insert at position 1; leave path[0] (directory at invocation) intact
sys.path.insert(1, os.path.join(this_file_path, '..'))

from argparse import ArgumentParser

from input.prismfile import PrismFile
from input.pctlfile import PctlFile
from input.resultfile import write_pstorm_result
from modelcheckers.param import ParamParametricModelChecker
from modelcheckers.storm import StormModelChecker
from modelcheckers.prism import PrismModelChecker

import config
from config import configuration

def parse_cli_args():
    parser = ArgumentParser(description='Transform a prism file to a rational function.')

    parser.add_argument('--file', help='the input file containing the prism file', required=True)
    parser.add_argument('--pctl-file', help='a file with a pctl property', required=True)
    parser.add_argument('--pctl-index', help='the index for the pctl file', default=0)
    parser.add_argument('--result-file', help='resulting file', default="result.out")
    solver_group = parser.add_mutually_exclusive_group(required=True)
    solver_group.add_argument('--param', action='store_true', help='use param via cli')
    solver_group.add_argument('--storm', action='store_true', help='use storm via cli')
    solver_group.add_argument('--prism', action='store_true', help='use prism via cli')
    solver_group.add_argument('--stormpy', action='store_true', help='use the python API')

    return parser.parse_args()


if __name__ == "__main__":
    pmcs = configuration.getAvailableParametricMCs()
    cmdargs = parse_cli_args()

    prism_file = PrismFile(cmdargs.file)
    pctl_file = PctlFile(cmdargs.pctl_file)

    if cmdargs.param:
        if 'param' not in  pmcs:
            raise RuntimeError("Param location not configured.")
        prism_file.make_temporary_copy()
        prism_file.replace_parameter_keyword("param float")
        tool = ParamParametricModelChecker()
    elif cmdargs.storm:
        if 'storm' not in  pmcs:
            raise RuntimeError("Storm location not configured.")
        tool = StormModelChecker()
    elif cmdargs.stormpy:
        if 'stormpy' not in  pmcs:
            raise RuntimeError("Stormpy dependency not configured.")
        from modelcheckers.stormpy import StormpyModelChecker
        tool = StormpyModelChecker()
    elif cmdargs.prism:
        if 'prism' not in  pmcs:
            raise RuntimeError("Prism location not configured.")
        tool = PrismModelChecker()
    else:
        raise RuntimeError("No supported model checker defined")

    print("Compute the rational function using " + tool.version())
    tool.load_model_from_prismfile(prism_file)
    tool.set_pctl_formula(pctl_file.get(cmdargs.pctl_index))
    result = tool.get_rational_function()
    write_pstorm_result(vars(cmdargs)["result_file"], result)

