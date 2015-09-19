#!/usr/bin/env python3

import os
import sys

# import library. Using this instead of appends prevents naming clashes..
this_file_path = os.path.dirname(os.path.realpath(__file__))
# insert at position 1; leave path[0] (directory at invocation) intact
sys.path.insert(1, os.path.join(this_file_path, '../prophesy'))

from argparse import ArgumentParser

from shapely.geometry.polygon import Polygon

from constraints.constraint_planes import ConstraintPlanes
from constraints.constraint_polygon import ConstraintPolygon
from constraints.constraint_quads import ConstraintQuads
from constraints.constraint_rectangles import ConstraintRectangles
from input.resultfile import read_pstorm_result
from output.plot import Plot
from sampling.sampling import read_samples_file
from smt.isat import IsatSolver
from smt.smt import setup_smt
from smt.smtlib import SmtlibSolver


def parse_cli_args():
    parser = ArgumentParser(description='Build constraints based on a sample file')

    parser.add_argument('--rat-file', help='file containing rational function', required=True)
    parser.add_argument('--samples-file', help='file containing the sample points', required=True)

    limit_group = parser.add_mutually_exclusive_group(required=True)
    limit_group.add_argument('--iterations', dest='iterations', help='Number of constraints to generate', type=int)
    limit_group.add_argument('--area', dest='area', help='Area (in [0,1]) to try to complete', type=float)

    method_group = parser.add_mutually_exclusive_group(required=True)
    method_group.add_argument('--planes', action='store_true', dest='planes')
    method_group.add_argument('--rectangles', action='store_true', dest='rectangles')
    method_group.add_argument('--quads', action='store_true', dest='quads')
    method_group.add_argument('--poly', action='store_true', dest='poly')

    solvers_group = parser.add_mutually_exclusive_group(required=True)
    solvers_group.add_argument('--z3', dest='z3location', help='location of z3')
    solvers_group.add_argument('--isat', dest='isatlocation', help='location of isat')

    parser.add_argument('--threshold-area', type=float, help='threshold for minimal size of new area', default=0.001)

    group = parser.add_mutually_exclusive_group()
    group.add_argument('--safe-above-threshold', action='store_true', dest='safe_above_threshold')
    group.add_argument('--bad-above-threshold', action='store_false', dest='safe_above_threshold')

    return parser.parse_args()


if __name__ == "__main__":
    cmdargs = parse_cli_args()

    threshold_area = cmdargs.threshold_area
    result = read_pstorm_result(cmdargs.rat_file)

    # is this still needed?
    if not cmdargs.safe_above_threshold:
        Plot.flip_green_red = True

    print("Loading samples")
    parameters, threshold, samples = read_samples_file(cmdargs.samples_file)
    print("Threshold: {}".format(threshold))
    print(samples)

    print("Setup SMT interface")
    if cmdargs.z3location:
        smt2interface = SmtlibSolver(cmdargs.z3location)
    elif cmdargs.isatlocation:
        smt2interface = IsatSolver(cmdargs.isatlocation)
    smt2interface.run()
    setup_smt(smt2interface, result, threshold)

    print("Generating constraints")
    generator = None
    params = samples, result.parameters, threshold, threshold_area, smt2interface, result.ratfunc

    if cmdargs.planes:
        generator = ConstraintPlanes(*params)
    elif cmdargs.rectangles:
        generator = ConstraintRectangles(*params)
    elif cmdargs.quads:
        generator = ConstraintQuads(*params)
    elif cmdargs.poly:
        generator = ConstraintPolygon(*params)
        # For testing
        generator.add_polygon(Polygon([(0, 0), (0.5, 0.5), (0.5, 0)]), True)
        generator.add_polygon(Polygon([(1, 0.25), (0.75, 0.5), (0.5, 0.25)]), True)
    else:
        assert False

    if cmdargs.iterations is not None:
        generator.generate_constraints(cmdargs.iterations)
    else:
        generator.generate_constraints(cmdargs.area)

    smt2interface.stop()
