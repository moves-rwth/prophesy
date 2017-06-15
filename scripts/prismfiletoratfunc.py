#!/usr/bin/env python3
import sys
from argparse import ArgumentParser
import logging


from prophesy.data.constant import parse_constants_string
from prophesy.input.prismfile import PrismFile
from prophesy.input.pctlfile import PctlFile
from prophesy.input.resultfile import write_pstorm_result
from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.modelcheckers.prism import PrismModelChecker

from prophesy.config import configuration

def parse_cli_args(args):
    parser = ArgumentParser(description='Transform a prism file to a rational function.')

    parser.add_argument('--file', help='the input file containing the prism file', required=True)
    parser.add_argument('--pctl-file', help='a file with a pctl property', required=True)
    parser.add_argument('--pctl-index', help='the index for the pctl file', default=0)
    parser.add_argument('--result-file', help='resulting file', default="result.out")
    parser.add_argument('--constants', type=str, help='string with constants')

    solver_group = parser.add_mutually_exclusive_group(required=True)
    solver_group.add_argument('--storm', action='store_true', help='use storm via cli')
    solver_group.add_argument('--prism', action='store_true', help='use prism via cli')
    solver_group.add_argument('--stormpy', action='store_true', help='use the python API')

    return parser.parse_args(args)


def run(args = sys.argv[1:], interactive = True):
    pmcs = configuration.getAvailableParametricMCs()
    cmdargs = parse_cli_args(args)
    constants = parse_constants_string(cmdargs.constants)

    prism_file = PrismFile(cmdargs.file)
    pctl_file = PctlFile(cmdargs.pctl_file)

    if cmdargs.storm:
        if 'storm' not in pmcs:
            raise RuntimeError("Storm location not configured.")
        tool = StormModelChecker()
    elif cmdargs.stormpy:
        if 'stormpy' not in pmcs:
            raise RuntimeError("Stormpy dependency not configured.")
        from prophesy.modelcheckers.stormpy import StormpyModelChecker
        tool = StormpyModelChecker()
    elif cmdargs.prism:
        if 'prism' not in pmcs:
            raise RuntimeError("Prism location not configured.")
        tool = PrismModelChecker()
    else:
        raise RuntimeError("No supported model checker defined")

    logging.info("Compute the rational function using " + tool.version())
    tool.load_model_from_prismfile(prism_file, constants)
    tool.set_pctl_formula(pctl_file.get(cmdargs.pctl_index))
    result = tool.get_rational_function()
    write_pstorm_result(vars(cmdargs)["result_file"], result)

if __name__ == "__main__":
    run()
