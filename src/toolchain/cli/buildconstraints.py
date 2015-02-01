#!/usr/bin/env python3

import sys
import os
# import library. Using this instead of appends prevents naming clashes..
thisfilepath = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))

import argparse
import sampling
from data.constraint import Constraint
from smt.smtlib import SmtlibSolver
from smt.isat import IsatSolver
from smt.smt import VariableDomain
from constraints.constraint_rectangles import ConstraintRectangles
from constraints.constraint_planes import ConstraintPlanes
from constraints.constraint_polygon import ConstraintPolygon
from input.resultfile import read_pstorm_result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = 'Build constraints based on a sample file')

    parser.add_argument('--rat-file', help = "file containing rational function", required = True)
    parser.add_argument('--samples-file', help = 'file containing the sample points', required = True)
    parser.add_argument('--constraint-file', help = 'the file in which the constraints are stored', default = "constraints.out")
    parser.add_argument('--threshold', type = float, help = 'the threshold', required = True)
    group = parser.add_mutually_exclusive_group(required = True)
    group.add_argument('--safe-above-threshold', action = 'store_true', dest = "safe_above_threshold")
    group.add_argument('--bad-above-threshold', action = 'store_false', dest = "safe_above_threshold")
    method_group = parser.add_mutually_exclusive_group(required = True)
    method_group.add_argument('--planes', action = 'store_true', dest = "planes")
    method_group.add_argument('--growing-rectangles', action = 'store_false', dest = "planes")
    solvers_group = parser.add_mutually_exclusive_group(required = True)
    solvers_group.add_argument('--z3', dest = "z3location", help = "location of z3")
    solvers_group.add_argument('--isat', dest = "isatlocation", help = "location of isat")
    parser.add_argument('--threshold-area', type = float, help = 'threshold for minimial size of new area', default = 0.001)
    cmdargs = parser.parse_args()

    threshold = vars(cmdargs)["threshold"]
    threshold_area = vars(cmdargs)["threshold_area"]
    result = read_pstorm_result(vars(cmdargs)['rat_file'])
    if cmdargs.z3location:
        smt2interface = SmtlibSolver(cmdargs.z3location)
    elif cmdargs.isatlocation:
        smt2interface = IsatSolver(cmdargs.isatlocation)

    print("Performing sample refinement")
    (parameters, samples) = sampling.read_samples_file(vars(cmdargs)["samples_file"])
    sampler = sampling.RatFuncSampling(result.ratfunc, result.parameters)
    #new_samples = sampling.refine_sampling(samples, threshold, sampler, cmdargs.safe_above_threshold)
    #while len(new_samples) < 60 and len(new_samples) > 0:
    #    print(new_samples)
    #    print("#####")
    #    samples.update(new_samples)
    #    new_samples = sampling.refine_sampling(samples, threshold, sampler, cmdargs.safe_above_threshold, use_filter = True)
    #samples.update(new_samples)
    print(samples)

    print("Setup SMT interface")
    smt2interface.run()

    for p in result.parameters:
        smt2interface.add_variable(p.name, VariableDomain.Real)
    smt2interface.add_variable("safe", VariableDomain.Bool)
    smt2interface.add_variable("bad", VariableDomain.Bool)

    if cmdargs.safe_above_threshold:
        safe_relation = ">="
        bad_relation = "<="
    else:
        safe_relation = "<="
        bad_relation = ">="

    safe_constraint = Constraint(result.ratfunc.nominator - threshold * result.ratfunc.denominator, safe_relation, result.parameters)
    bad_constraint = Constraint(result.ratfunc.nominator - threshold * result.ratfunc.denominator, bad_relation, result.parameters)
    smt2interface.assert_guarded_constraint("safe", safe_constraint)
    smt2interface.assert_guarded_constraint("bad", bad_constraint)

    print("Generating constraints")
    generator = None
    if cmdargs.planes:
        generator = ConstraintPlanes(samples, result.parameters, threshold, cmdargs.safe_above_threshold, threshold_area, smt2interface, result.ratfunc)
    else:
        generator = ConstraintRectangles(samples, result.parameters, threshold, cmdargs.safe_above_threshold, threshold_area, smt2interface, result.ratfunc)
    generator.generate_constraints()

    # only for testing purposes of polygon
    #generator = ConstraintPolygon(samples, result.parameters, threshold, cmdargs.safe_above_threshold, threshold_area, smt2interface, result.ratfunc)
    #generator.add_polygon(Polygon([(0,0), (0.5, 0.5), (0.5, 0)]), True)
    #generator.add_polygon(Polygon([(0.5, 0), (0.75, 0.25), (0.5, 0.5), (0.25, 0.25)]), True)

    smt2interface.stop()
    #print("Executed SMT commands:")
    #smt2interface.print_calls()    