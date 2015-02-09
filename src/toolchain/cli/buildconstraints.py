#!/usr/bin/env python3

import sys
import os
from shapely.geometry.polygon import Polygon
from sampling.sampling import read_samples_file
# import library. Using this instead of appends prevents naming clashes..
thisfilepath = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))

import argparse
from smt.smtlib import SmtlibSolver
from smt.isat import IsatSolver
from smt.smt import setup_smt
from constraints.constraint_rectangles import ConstraintRectangles
from constraints.constraint_planes import ConstraintPlanes
from constraints.constraint_polygon import ConstraintPolygon
from constraints.constraint_quads import ConstraintQuads
from input.resultfile import read_pstorm_result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = 'Build constraints based on a sample file')

    parser.add_argument('--rat-file', help = "file containing rational function", required = True)
    parser.add_argument('--samples-file', help = 'file containing the sample points', required = True)
    limit_group = parser.add_mutually_exclusive_group(required = True)
    limit_group.add_argument('--iterations', dest = "iterations", help = "Number of constraints to generate", type=int)
    limit_group.add_argument('--area', dest = "area", help = "Area (in [0,1]) to try to complete", type = float)
    method_group = parser.add_mutually_exclusive_group(required = True)
    method_group.add_argument('--planes', action = 'store_true', dest = "planes")
    method_group.add_argument('--rectangles', action = 'store_true', dest = "rectangles")
    method_group.add_argument('--quads', action = 'store_true', dest = "quads")
    method_group.add_argument('--poly', action = 'store_true', dest = "poly")
    solvers_group = parser.add_mutually_exclusive_group(required = True)
    solvers_group.add_argument('--z3', dest = "z3location", help = "location of z3")
    solvers_group.add_argument('--isat', dest = "isatlocation", help = "location of isat")
    parser.add_argument('--threshold-area', type = float, help = 'threshold for minimal size of new area', default = 0.001)
    cmdargs = parser.parse_args()

    threshold_area = cmdargs.threshold_area
    result = read_pstorm_result(cmdargs.rat_file)

    print("Loading samples")
    (parameters, threshold, safe_above_threshold, samples) = read_samples_file(cmdargs.samples_file)
    print("Threshold: {}".format(threshold))
    print("Safe above threshold: {}".format(safe_above_threshold))
    print(samples)

    print("Setup SMT interface")
    if cmdargs.z3location:
        smt2interface = SmtlibSolver(cmdargs.z3location)
    elif cmdargs.isatlocation:
        smt2interface = IsatSolver(cmdargs.isatlocation)
    smt2interface.run()
    setup_smt(smt2interface, result, threshold, safe_above_threshold)

    print("Generating constraints")
    generator = None
    if cmdargs.planes:
        generator = ConstraintPlanes(samples, result.parameters, threshold, safe_above_threshold, threshold_area, smt2interface, result.ratfunc)
    elif cmdargs.rectangles:
        generator = ConstraintRectangles(samples, result.parameters, threshold, safe_above_threshold, threshold_area, smt2interface, result.ratfunc)
    elif cmdargs.quads:
        generator = ConstraintQuads(samples, result.parameters, threshold, safe_above_threshold, threshold_area, smt2interface, result.ratfunc)
    elif cmdargs.poly:
        generator = ConstraintPolygon(samples, result.parameters, threshold, safe_above_threshold, threshold_area, smt2interface, result.ratfunc)
        # For testing
        generator.add_polygon(Polygon([(0,0), (0.5, 0.5), (0.5, 0)]), True)
        generator.add_polygon(Polygon([(1, 0.25), (0.75, 0.5), (0.5, 0.25)]), True)
    else:
        assert False

    if cmdargs.iterations != None:
        generator.generate_constraints(cmdargs.iterations)
    else:
        generator.generate_constraints(cmdargs.area)

    smt2interface.stop()
