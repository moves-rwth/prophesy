#!/usr/bin/env python3

import sys
import os
# import library. Using this instead of appends prevents naming clashes..
thisfilepath = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))

import argparse
from input.prismfile import PrismFile
from modelcheckers.param import ParamParametricModelChecker
from modelcheckers.pstorm import ProphesyParametricModelChecker
from input.resultfile import write_result_file

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = 'Transform a prism file to a rational function.')

    parser.add_argument('--file', help = 'the input file containing the prism file', required = True)
    parser.add_argument('--pctl-file', help = 'a file with a pctl property', required = True)
    parser.add_argument('--result-file', help = 'resulting file', default = "result.out")

    solver_group = parser.add_mutually_exclusive_group(required = True)
    solver_group.add_argument('--param', help = 'call the param tool')
    solver_group.add_argument('--pstorm', help = 'the location of the pstorm binary')
    solver_group.add_argument('--comics', help = 'the location of the comics binary')
    cmdargs = parser.parse_args()


    prism_file = PrismFile(vars(cmdargs)["file"])

    if vars(cmdargs)["param"] != None:
        prism_file.make_temporary_copy()
        prism_file.replace_parameter_keyword("param float")
        tool = ParamParametricModelChecker(vars(cmdargs)["param"])
    elif vars(cmdargs)["pstorm"] != None:
        tool = ProphesyParametricModelChecker(vars(cmdargs)["pstorm"])
    elif vars(cmdargs)["comics"] != None:
        raise NotImplementedError
    else:
        raise RuntimeError("No supported solver available")

    print("Compute the rational function using " + tool.version())
    result = tool.get_rational_function(prism_file, vars(cmdargs)["pctl_file"])
    write_result_file(result[0], result[1], result[2], result[3], vars(cmdargs)["result_file"])

