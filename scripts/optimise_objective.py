#!/usr/bin/env python3

from argparse import ArgumentParser
import sys
import logging
import os

import prophesy.adapter.pycarl as pc
from prophesy.optimisation.simple_binary_search import BinarySearchOptimisation
from prophesy.script_utilities.init_solvers_and_problems import init_solvers_and_problem
from prophesy.util import open_file

logger = logging.getLogger(__name__)


def _get_argparser():
    parser = ArgumentParser(description='Build regions based on a sample file')

    parser.add_argument('--rat-file', help='file containing rational function')
    parser.add_argument('--model-file', help='file containing the model')
    parser.add_argument('--constants', type=str, help='string with constants for model')
    parser.add_argument('--property-file', help='file containing the property')
    parser.add_argument('--samples-file', help='file containing the sample points')
    parser.add_argument('--log-calls', help='file where we print the smt2 calls', dest='logcallsdestination',
                        required=False)

    limit_group = parser.add_mutually_exclusive_group(required=True)
    limit_group.add_argument('--iterations', dest='iterations', help='Number of regions to generate', type=int)
    limit_group.add_argument('--gap', dest='gap', help='Gap between upper and lower bound', type=float)

    region_group = parser.add_mutually_exclusive_group(required=True)
    region_group.add_argument('--rectangles', action='store_true', dest='rectangles')
    region_group.add_argument('--quads', action='store_true', dest='quads')
    region_group.add_argument('--poly', action='store_true', dest='poly')

    method_group = parser.add_mutually_exclusive_group(required=True)
    method_group.add_argument('--pla', action='store_true')
    method_group.add_argument('--sfsmt', action='store_true')
    method_group.add_argument('--etr', action='store_true')

    solvers_group = parser.add_mutually_exclusive_group(required=False)
    solvers_group.add_argument('--z3', action='store_true', help="Use Z3 (SMT)")
    solvers_group.add_argument('--isat', action='store_true', help="Use Isat (ICP)")
    solvers_group.add_argument('--yices', action='store_true', help="Use Yices (SMT)")

    modelchecker_group = parser.add_mutually_exclusive_group(required=False)
    modelchecker_group.add_argument("--storm", action="store_true", help="Use storm")
    modelchecker_group.add_argument("--stormpy", action="store_true", help="Use stormpy")

    parser.add_argument('--bad-above-threshold', action='store_false', dest='safe_above_threshold', default=True)

    graph_preservation_type = parser.add_mutually_exclusive_group(required=False)
    graph_preservation_type.add_argument('--epsilon-pmc', type=pc.Rational,
                        help="if set, uses this epsilon as an offset to the parameter values")
    graph_preservation_type.add_argument('--graph-preserving-pmc', action='store_true')

    plot_group = parser.add_argument_group("Plotting")
    plot_group.add_argument("--plot-every-n", type=int, default=10000000)
    plot_group.add_argument("--plot-candidates", action="store_true", default=False)

    return parser


def parse_cli_args(args):
    return _get_argparser().parse_args(args)


def run(args=sys.argv[1:], interactive=False):
    cmdargs = parse_cli_args(args)
    problem_description, region_checker, samples, solver = init_solvers_and_problem(cmdargs, True)

    optimiser = BinarySearchOptimisation(region_checker, problem_description)

    # TODO set plot frequency
    if cmdargs.iterations is not None:
        optimiser.search()
    else:
        optimiser.search()


    if not cmdargs.storm and not cmdargs.stormpy:
        solver.stop()

    if cmdargs.logcallsdestination:
        solver.to_file(cmdargs.logcallsdestination)


if __name__ == "__main__":
    run()
