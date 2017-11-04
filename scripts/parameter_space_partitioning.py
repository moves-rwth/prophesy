#!/usr/bin/env python3

from argparse import ArgumentParser
import sys
import logging

import prophesy.adapter.pycarl as pc
from prophesy.regions.region_quads import HyperRectangleRegions
from prophesy.script_utilities.init_solvers_and_problems import init_solvers_and_problem
from prophesy.util import open_file
from prophesy.output.plot import Plot

logger = logging.getLogger(__name__)


def _get_argparser():
    parser = ArgumentParser(description='Build regions based on a sample file')


    parser.add_argument('--log-calls', help='file where we print the smt2 calls', dest='logcallsdestination',
                        required=False)



    graph_preservation_type = parser.add_mutually_exclusive_group(required=False)
    graph_preservation_type.add_argument('--epsilon-pmc', type=pc.Rational,
                        help="if set, uses this epsilon as an offset to the parameter values")
    graph_preservation_type.add_argument('--graph-preserving-pmc', action='store_true')


    return parser


def parse_cli_args(args):
    return _get_argparser().parse_args(args)


def run(args=sys.argv[1:], interactive=False):
    cmdargs = parse_cli_args(args)

    problem_description, region_checker, samples, solver, mc = init_solvers_and_problem(cmdargs)

    # TODO set plot frequency
    if cmdargs.iterations is not None:
        generator.generate_constraints(max_iter=cmdargs.iterations, plot_every_n=cmdargs.plot_every_n,
                                       plot_candidates=cmdargs.plot_candidates)
    else:
        generator.generate_constraints(max_area=pc.Rational(cmdargs.area), plot_every_n=cmdargs.plot_every_n,
                                       plot_candidates=cmdargs.plot_candidates)

    if interactive:
        open_file(generator.result_file)

    if not cmdargs.storm and not cmdargs.stormpy:
        solver.stop()

    if cmdargs.logcallsdestination:
        solver.to_file(cmdargs.logcallsdestination)


if __name__ == "__main__":
    run()
