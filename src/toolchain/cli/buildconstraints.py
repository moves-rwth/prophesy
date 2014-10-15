#!/usr/bin/env python3

"""

"""
import sys
import os
# import library. Using this instead of appends prevents naming clashes..
thisfilepath =  os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))


import argparse
import sympy

import util
import sampling
import constraint_generation
from input.resultfile import *
from smt.smtlib import SmtlibSolver
from smt.smt import VariableDomain

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Build constraints based on a sample file')
    
    parser.add_argument('--rat-file', help="file containing rational function", required=True)
    parser.add_argument('--samples-file', help='file containing the sample points')
    parser.add_argument('--constraint-file', help='the file in which the constraints are stored')
    parser.add_argument('--threshold', type=float, help='the threshold', required=True)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--safe-above-threshold', action='store_true', dest="safe_above_threshold")
    group.add_argument('--bad-above-threshold', action='store_false', dest="safe_above_threshold")
    method_group = parser.add_mutually_exclusive_group(required=True)
    method_group.add_argument('--planes', action='store_true', dest="planes")
    method_group.add_argument('--growing-rectangles', action='store_false', dest="planes")
    solvers_group = parser.add_mutually_exclusive_group(required=True)
    solvers_group.add_argument('--z3', dest="z3location", help="location of z3")
    cmdargs = parser.parse_args()
    
    threshold = vars(cmdargs)["threshold"]
    [ratfunc_parameters, wdconstraints, gpconstraints, ratfunc] = parse_result_file(vars(cmdargs)['rat_file'])
    
    smt2interface = SmtlibSolver(cmdargs.z3location)
    smt2interface.run()
    for p in ratfunc_parameters:
        smt2interface.add_variable(p.name, VariableDomain.Real)
    smt2interface.add_variable("_safe_", VariableDomain.Bool)
    smt2interface.add_variable("_bad_", VariableDomain.Bool)
    
    if cmdargs.safe_above_threshold:
        safe_relation = ">="
        bad_relation = "<"
    else:
        safe_relation = "<="
        bad_relation = ">"
        
    safe_objective_constraint = Constraint(ratfunc.nominator - threshold * ratfunc.denominator, safe_relation, ratfunc_parameters)
    bad_objective_constraint = Constraint(ratfunc.nominator - threshold * ratfunc.denominator, bad_relation ,ratfunc_parameters)
    
    smt2interface.assert_guarded_constraint("_safe_", safe_objective_constraint)
    smt2interface.assert_guarded_constraint("_bad_", bad_objective_constraint)
            
    smt2interface.print_calls()        
    
    (samples, parameters) = sampling.parse_samples_file(vars(cmdargs)["samples_file"])
    samples = sampling.refine_sampling(samples, threshold, sampling.RatFuncSampling(ratfunc, ratfunc_parameters),  cmdargs.safe_above_threshold)
    samples = sampling.refine_sampling(samples, threshold, sampling.RatFuncSampling(ratfunc, ratfunc_parameters),  cmdargs.safe_above_threshold)
    
    if cmdargs.planes:
        print(constraint_generation.create_halfspace_constraint(samples, ratfunc_parameters, vars(cmdargs)["threshold"], cmdargs.safe_above_threshold))
    else:
        constraint_generation.growing_rectangle_constraints(samples, ratfunc_parameters, vars(cmdargs)["threshold"], cmdargs.safe_above_threshold, smt2interface, ratfunc)
    