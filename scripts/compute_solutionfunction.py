#!/usr/bin/env python3

import sys
from argparse import ArgumentParser
import logging

from prophesy.data.constant import parse_constants_string
from prophesy.input.prismfile import PrismFile
from prophesy.input.pctlfile import PctlFile
from prophesy.input.solutionfunctionfile import write_pstorm_result
from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.config import configuration


def _get_argparser():
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

    return parser


def parse_cli_args(args):
    return _get_argparser().parse_args(args)


def run(args=sys.argv[1:], interactive=True):
    cmdargs = parse_cli_args(args)
    configuration.check_tools()
    pmcs = configuration.getAvailableParametricMCs()
    constants = parse_constants_string(cmdargs.constants)

    prism_file = PrismFile(cmdargs.file)
    if prism_file.contains_nondeterministic_model():
        raise NotImplementedError("Solution functions are not suppported for nondeterministic models")
    pctl_file = PctlFile(cmdargs.pctl_file)

    if cmdargs.storm:
        if 'storm' not in pmcs:
            raise RuntimeError("Storm location not configured.")
        tool = StormModelChecker()
    elif cmdargs.prism:
        if 'prism' not in pmcs:
            raise RuntimeError("Prism location not configured.")
        tool = PrismModelChecker()
    elif cmdargs.stormpy:
        if 'stormpy' not in pmcs:
            raise RuntimeError("Stormpy dependency not configured.")
        from prophesy.modelcheckers.stormpy import StormpyModelChecker
        tool = StormpyModelChecker()
    else:
        raise RuntimeError("No supported model checker defined")

    logging.info("Compute the rational function using " + tool.name() + " "+ tool.version())
    tool.load_model_from_prismfile(prism_file, constants)
    tool.set_pctl_formula(pctl_file.get(cmdargs.pctl_index))
    result = tool.get_rational_function()
    problem_parameters = [p for p in prism_file.parameters if not constants.has_variable(p.variable)]
    if problem_parameters != result.parameters:
        if len(problem_parameters) != len(result.parameters):
            raise ValueError(
                "Parameters in model '{}' and in result '{}' do not coincide.".format(prism_file.parameters,
                                                                                      result.parameters))
        for p in problem_parameters:
            if p not in result.parameters:
                raise ValueError(
                    "Parameters in model '{}' and in result '{}' do not coincide.".format(prism_file.parameters,
                                                                                          result.parameters))
        result.parameters = prism_file.parameters
    write_pstorm_result(vars(cmdargs)["result_file"], result)


if __name__ == "__main__":
    run()
