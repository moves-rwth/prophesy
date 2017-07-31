#!/usr/bin/env python3

from argparse import ArgumentParser
import sys
import logging

import prophesy.adapter.pycarl as pc
from prophesy.regions.region_polygon import ConstraintPolygon
from prophesy.regions.region_quads import HyperRectangleRegions
from prophesy.regions.region_smtchecker import SmtRegionChecker
from prophesy.regions.region_plachecker import PlaRegionChecker
from prophesy.regions.region_checker import ProblemDescription
from prophesy.input.solutionfunctionfile import read_pstorm_result
from prophesy.input.prismfile import PrismFile
from prophesy.input.pctlfile import PctlFile
from prophesy.output.plot import Plot
from prophesy.input.samplefile import read_samples_file
from prophesy.util import open_file
from prophesy.smt.isat import IsatSolver
from prophesy.smt.smtlib import SmtlibSolver
from prophesy.smt.Z3cli_solver import Z3CliSolver
from prophesy.smt.YicesCli_solver import YicesCLISolver
from prophesy.modelcheckers.storm import StormModelChecker
from prophesy import config
from prophesy.config import configuration

logger = logging.getLogger(__name__)


def _get_argparser():
    parser = ArgumentParser(description='Build regions based on a sample file')

    parser.add_argument('--rat-file', help='file containing rational function')
    parser.add_argument('--model-file', help='file containing the model')
    parser.add_argument('--property-file', help='file containing the property')
    parser.add_argument('--samples-file', help='file containing the sample points', required=True)
    parser.add_argument('--log-calls', help='file where we print the smt2 calls', dest='logcallsdestination',
                        required=False)
    parser.add_argument('--threshold', help='gives the threshold', type=pc.Rational, required=True)

    limit_group = parser.add_mutually_exclusive_group(required=True)
    limit_group.add_argument('--iterations', dest='iterations', help='Number of regions to generate', type=int)
    limit_group.add_argument('--area', dest='area', help='Area (in [0,1]) to try to complete', type=float)

    method_group = parser.add_mutually_exclusive_group(required=True)
    method_group.add_argument('--rectangles', action='store_true', dest='rectangles')
    method_group.add_argument('--quads', action='store_true', dest='quads')
    method_group.add_argument('--poly', action='store_true', dest='poly')

    solvers_group = parser.add_mutually_exclusive_group(required=True)
    solvers_group.add_argument('--z3', action='store_true', help="Use Z3 (SMT)")
    solvers_group.add_argument('--isat', action='store_true', help="Use Isat (ICP)")
    solvers_group.add_argument('--yices', action='store_true', help="Use Yices (SMT)")
    solvers_group.add_argument('--storm', action="store_true", help="Use Storm (PLA)")
    solvers_group.add_argument('--stormpy', action="store_true", help="Use Stormpy (PLA)")

    parser.add_argument('--bad-above-threshold', action='store_false', dest='safe_above_threshold', default=True)
    parser.add_argument('--epsilon-pmc', type=pc.Rational,
                        help="if set, uses this epsilon as an offset to the parameter values")

    return parser


def parse_cli_args(args):
    return _get_argparser().parse_args(args)


def run(args=sys.argv[1:], interactive=False):
    solvers = configuration.getAvailableSMTSolvers()
    ppmcs = configuration.getAvailableParametricMCs()
    cmdargs = parse_cli_args(args)
    configuration.check_tools()

    problem_description = ProblemDescription()

    if cmdargs.rat_file:
        result = read_pstorm_result(cmdargs.rat_file)
        parameters = result.parameters
        problem_description.solutionfunction = result
    if cmdargs.model_file:
        model_file = PrismFile(cmdargs.model_file)
        if not cmdargs.property_file:
            raise RuntimeError("Property file needed when model file is given.")
        properties = PctlFile(cmdargs.property_file)
        if cmdargs.rat_file and parameters != model_file.parameters:
            raise ValueError("Model file and solution function parameters do not coincide")
        parameters = model_file.parameters
        problem_description.model = model_file
        problem_description.property = properties.get(0)

    if cmdargs.epsilon_pmc:
        parameters.make_intervals_closed(cmdargs.epsilon_pmc)

    if not cmdargs.safe_above_threshold:
        Plot.flip_green_red = True

    logger.debug("Loading samples")
    sample_parameters, samples_threshold, samples = read_samples_file(cmdargs.samples_file, parameters)
    if parameters != sample_parameters:
        raise RuntimeError("Sampling and problem parameters are not equal")

    # TODO allow setting threshold via property
    if cmdargs.threshold:
        threshold = cmdargs.threshold
    logger.debug("Threshold: {}".format(threshold))

    logger.debug("Setup Region Checker Interface")
    if cmdargs.z3:
        if 'z3' not in solvers:
            raise RuntimeError("Z3 location not configured.")
        backend = Z3CliSolver()
        backend.run()
        checker = SmtRegionChecker(backend, parameters)
    elif cmdargs.yices:
        if 'yices' not in solvers:
            raise RuntimeError("Yices location not configured.")
        backend = YicesCLISolver()
        backend.run()
        checker = SmtRegionChecker(backend, parameters)
    elif cmdargs.isat:
        if 'isat' not in solvers:
            raise RuntimeError("ISat location not configured.")
        backend = IsatSolver()
        backend.run()
        checker = SmtRegionChecker(backend, parameters)
    elif cmdargs.storm:
        if 'storm-pars' not in ppmcs:
            raise RuntimeError("Storm location not configured.")
        backend = StormModelChecker()
        checker = PlaRegionChecker(backend, parameters)
    elif cmdargs.stormpy:
        if 'stormpy' not in ppmcs:
            raise RuntimeError("Stormpy dependency not configured.")
        # Do not import at top, as stormpy might not be available.
        from prophesy.modelcheckers.stormpy import StormpyModelChecker
        backend = StormpyModelChecker()
        checker = PlaRegionChecker(backend, parameters)
    else:
        raise RuntimeError("No supported region checker defined.")

    logger.info("Generating regions")
    checker.initialize(problem_description, threshold)
    arguments = samples, parameters, threshold, checker

    if cmdargs.rectangles:
        raise NotImplementedError("Rectangles are currently not supported.")
    elif cmdargs.quads:
        generator = HyperRectangleRegions(*arguments)
    elif cmdargs.poly:
        generator = ConstraintPolygon(*arguments)
        # For testing
    else:
        raise RuntimeError("No supported region type defined.")

    if cmdargs.iterations is not None:
        generator.generate_constraints(max_iter=cmdargs.iterations)
    else:
        generator.generate_constraints(max_area=pc.Rational(cmdargs.area))

    if interactive:
        open_file(generator.result_file)

    if not cmdargs.storm and not cmdargs.stormpy:
        backend.stop()

    if cmdargs.logcallsdestination:
        backend.to_file(cmdargs.logcallsdestination)


if __name__ == "__main__":
    run()
