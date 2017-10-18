#!/usr/bin/env python3

from argparse import ArgumentParser
import sys
import logging
import os

import prophesy.adapter.pycarl as pc
from prophesy.optimisation.simple_binary_search import BinarySearchOptimisation
from  prophesy.optimisation.pla_based_search import PlaSearchOptimisation
from prophesy.script_utilities.init_solvers_and_problems import init_solvers_and_problem
from prophesy.optimisation.heuristic_search import ModelOptimizer
from prophesy.data.property import OperatorType, OperatorDirection
from prophesy.util import open_file
from prophesy.regions.welldefinedness import SampleWelldefinedChecker
from prophesy.smt.isat import IsatSolver
from prophesy.smt.Z3cli_solver import Z3CliSolver
from prophesy.smt.YicesCli_solver import YicesCLISolver
from prophesy.sampling.sampler_ratfunc import RatFuncSampling


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


    parser.add_argument('--compute-bound', action="store_true", dest='bounding', help="Should we bound the optimal value by expensive computations")
    parser.add_argument('--iterations', dest='iterations', help='Number of regions to generate', type=int, default=10000)
    parser.add_argument('--gap', dest='gap', help='Gap between upper and lower bound', type=pc.Rational, default=pc.Rational("0.08"))

    region_group = parser.add_mutually_exclusive_group(required=True)
    region_group.add_argument('--rectangles', action='store_true', dest='rectangles')
    region_group.add_argument('--quads', action='store_true', dest='quads')

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

    graph_preservation_type = parser.add_mutually_exclusive_group(required=False)
    graph_preservation_type.add_argument('--epsilon-pmc', type=pc.Rational,
                        help="if set, uses this epsilon as an offset to the parameter values")
    graph_preservation_type.add_argument('--graph-preserving-pmc', action='store_true')


    return parser


def parse_cli_args(args):
    return _get_argparser().parse_args(args)


def run(args=sys.argv[1:], interactive=False):
    cmdargs = parse_cli_args(args)
    problem_description, region_checker, samples, solver, mc = init_solvers_and_problem(cmdargs, True)

    solver2 = None
    if cmdargs.z3:
        solver2 = Z3CliSolver()
        solver2.run()
    elif cmdargs.yices:
        solver2 = YicesCLISolver()
        solver2.run()
    elif cmdargs.isat:
        solver2 = IsatSolver()
        solver2.run()

    assert problem_description.property.operator_direction != OperatorDirection.unspecified
    optimal_dir = "max" if problem_description.property.operator_direction == OperatorDirection.max else "min"
    assert problem_description.welldefined_constraints is not None
    if mc:
        mc.set_welldefined_checker(SampleWelldefinedChecker(solver2, problem_description.parameters,problem_description.welldefined_constraints))
        optimizer = ModelOptimizer(mc, problem_description.parameters, problem_description.property, optimal_dir)
        _, val = optimizer.search()
        score = optimizer.score(None, val)
        print("RESULT: {}".format(float(score)))
    else:
        optimizer = ModelOptimizer(RatFuncSampling(problem_description.parameters, problem_description.parameters), problem_description.parameters, problem_description.property, optimal_dir)
        _, val = optimizer.search()
        score = optimizer.score(None, val)
        print("RESULT: {}".format(float(score)))
        #score = pc.Rational(200000000000000)
    #result_as_instantiation = ParameterInstantiation.from_point(Point(*location), problem_description.parameters)

    if cmdargs.bounding:
        if cmdargs.pla:
            #TODO do not rely on internal member
            optimiser = PlaSearchOptimisation(region_checker._checker, problem_description)
        else:
            optimiser = BinarySearchOptimisation(region_checker, problem_description)

        if problem_description.property.operator_direction == OperatorDirection.max:
            if problem_description.property.operator == OperatorType.reward:
                bound = pc.inf
            else:
                bound = pc.Rational(1)
        else:
            bound = pc.Rational(0)
        optimiser.search(requested_gap=cmdargs.gap, max_iterations=cmdargs.iterations, dir=optimal_dir, realised=score, bound=bound)


    if not cmdargs.storm and not cmdargs.stormpy:
        solver.stop()

    if cmdargs.logcallsdestination:
        solver.to_file(cmdargs.logcallsdestination)


if __name__ == "__main__":
    run()
