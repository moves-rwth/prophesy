#!/usr/bin/env python3

from argparse import ArgumentParser

import sys

from shapely.geometry.polygon import Polygon

from prophesy.regions.region_polygon import ConstraintPolygon
from prophesy.regions.region_quads import ConstraintQuads
from prophesy.regions.region_smtchecker import SmtRegionChecker
from prophesy.input.resultfile import read_pstorm_result
from prophesy.output.plot import Plot
from prophesy.input.samplefile import read_samples_file
from prophesy.util import open_file
from prophesy.smt.isat import IsatSolver
from prophesy.smt.smt import setup_smt
from prophesy.smt.smtlib import SmtlibSolver
from prophesy.smt.Z3cli_solver import Z3CliSolver

from prophesy import config
from prophesy.config import configuration

def parse_cli_args(args, solversConfig):
    parser = ArgumentParser(description='Build regions based on a sample file')

    parser.add_argument('--rat-file', help='file containing rational function', required=True)
    parser.add_argument('--samples-file', help='file containing the sample points', required=True)
    parser.add_argument('--log-calls', help='file where we print the smt2 calls', dest='logcallsdestination', required = False)
    parser.add_argument('--threshold', help='gives the threshold', type=float)

    limit_group = parser.add_mutually_exclusive_group(required=True)
    limit_group.add_argument('--iterations', dest='iterations', help='Number of regions to generate', type=int)
    limit_group.add_argument('--area', dest='area', help='Area (in [0,1]) to try to complete', type=float)

    method_group = parser.add_mutually_exclusive_group(required=True)
    method_group.add_argument('--rectangles', action='store_true', dest='rectangles')
    method_group.add_argument('--quads', action='store_true', dest='quads')
    method_group.add_argument('--poly', action='store_true', dest='poly')

    solvers_group = parser.add_mutually_exclusive_group(required=not solversConfig)
    solvers_group.add_argument('--z3', dest='z3location', help='location of z3')
    solvers_group.add_argument('--isat', dest='isatlocation', help='location of isat')

    parser.add_argument('--solver-timeout', help='timeout (s) for solver backend', default=50, type=int)
    parser.add_argument('--solver-memout', help='memout (MB) for solver backend', default=4000, type=int)

    parser.add_argument('--threshold-area', type=float, help='threshold for minimal size of new area', default=0.001)

    parser.add_argument('--bad-above-threshold', action='store_false', dest='safe_above_threshold', default=True)

    return parser.parse_args(args)

def run(args = sys.argv[1:], interactive=True):
    solvers = configuration.getAvailableSMTSolvers()
    cmdargs = parse_cli_args(args, solvers)

    threshold_area = cmdargs.threshold_area
    result = read_pstorm_result(cmdargs.rat_file)

    if not cmdargs.safe_above_threshold:
        Plot.flip_green_red = True

    print("Loading samples")
    variables, samples_threshold, samples = read_samples_file(cmdargs.samples_file, result.parameters.get_variables())
    if result.parameters.get_variables() != variables:
        raise RuntimeError("Sampling and Result parameters are not equal")

    if cmdargs.threshold:
        threshold = cmdargs.threshold
    else:
        print("Using threshold from samples file.")
        threshold = samples_threshold

    if threshold == None:
        raise RuntimeError("No threshold specified via command line or samples file.")
    print("Threshold: {}".format(threshold))



    print("Setup SMT interface")
    if cmdargs.z3location:
        smt2interface = Z3CliSolver(cmdargs.z3location, timeout=cmdargs.solver_timeout, memout=cmdargs.solver_memout)
    elif cmdargs.isatlocation:
        smt2interface = IsatSolver(cmdargs.isatlocation)
    elif 'z3' in solvers:
        smt2interface = Z3CliSolver(configuration.get(config.EXTERNAL_TOOLS, "z3"))
    elif 'isat' in solvers:
        smt2interface = IsatSolver(configuration.get(config.EXTERNAL_TOOLS, "isat"))
    else:
        raise RuntimeError("No supported SMT defined")

    smt2interface.run()

    setup_smt(smt2interface, result, threshold)

    print("Generating regions")
    checker = SmtRegionChecker(smt2interface, result.parameters, result.ratfunc)
    arguments = samples, result.parameters, threshold, threshold_area, checker, result.ratfunc

    if cmdargs.rectangles:
        raise NotImplementedError("Rectangles are currently not supported")
    elif cmdargs.quads:
        generator = ConstraintQuads(*arguments)
    elif cmdargs.poly:
        generator = ConstraintPolygon(*arguments)
        # For testing
        generator.add_polygon(Polygon([(0, 0), (0.5, 0.5), (0.5, 0)]), False)
        generator.add_polygon(Polygon([(1, 0.25), (0.75, 0.5), (0.5, 0.25)]), False)
    else:
        assert False

    if cmdargs.iterations is not None:
        generator.generate_constraints(max_iter = cmdargs.iterations)
    else:
        generator.generate_constraints(max_area = cmdargs.area)

    if interactive:
        open_file(generator.result_file)

    if cmdargs.logcallsdestination:
        smt2interface.to_file(cmdargs.logcallsdestination)

    smt2interface.stop()


if __name__ == "__main__":
    run()
