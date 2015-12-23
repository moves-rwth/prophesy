#!/usr/bin/env python3

import os
import sys

# import library. Using this instead of appends prevents naming clashes..
this_file_path = os.path.dirname(os.path.realpath(__file__))
# insert at position 1; leave path[0] (directory at invocation) intact
sys.path.insert(1, os.path.join(this_file_path, '../prophesy'))

from argparse import ArgumentParser

from input.prismfile import PrismFile
from input.resultfile import write_pstorm_result
from modelcheckers.param import ParamParametricModelChecker
from modelcheckers.storm import StormModelChecker


def parse_cli_args():
    parser = ArgumentParser(description='Transform a prism file to a rational function.')

    parser.add_argument('--file', help='the input file containing the prism file', required=True)
    parser.add_argument('--pctl-file', help='a file with a pctl property', required=True)
    parser.add_argument('--result-file', help='resulting file', default="result.out")

    solver_group = parser.add_mutually_exclusive_group(required=True)
    solver_group.add_argument('--param', help='call the param tool')
    solver_group.add_argument('--storm', help='the location of the pstorm binary')
    solver_group.add_argument('--comics', help='the location of the comics binary')

    return parser.parse_args()


if __name__ == "__main__":
    cmdargs = parse_cli_args()

    prism_file = PrismFile(cmdargs.file)

    if cmdargs.param is not None:
        prism_file.make_temporary_copy()
        prism_file.replace_parameter_keyword("param float")
        tool = ParamParametricModelChecker(cmdargs.param)
    elif cmdargs.storm is not None:
        tool = StormModelChecker(cmdargs.storm)
    elif cmdargs.comics is not None:
        tool = ParamParametricModelChecker(vars(cmdargs)["param"])
    else:
        raise RuntimeError("No supported solver available")

    print("Compute the rational function using " + tool.version())
    result = tool.get_rational_function(prism_file, vars(cmdargs)["pctl_file"])
    write_pstorm_result(vars(cmdargs)["result_file"], result)

