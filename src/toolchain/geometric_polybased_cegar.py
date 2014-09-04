#!/bin/python3
import argparse
import math
import re
from data.constraint import Constraint
from data.rationalfunction import RationalFunction
from sympy.polys import Poly
import iterable_param
from input.comics import *
from input.additional_constraints import *
from output.output import *
from output.smt2 import *
from output.plot import *
from output.samplepoints import *
import shlex
import subprocess
import os

def generate_constraints(samplepoint_filepath, add_constraints_filepath):
    call = CONSTRAINT_GENERATION_COMMAND + " --file " + samplepoint_filepath + " --out " + add_constraints_filepath
    args = shlex.split(call)
    print(call)
    pipe = subprocess.Popen(args, stdout=subprocess.PIPE)
    #pipe.communicate()
    output =  pipe.communicate()[0]

def generate_samples():
    pass

def inside(parameters, p, constraints):
    return check_samplepoint_smt2(parameters, p, constraints)
    

def remove_covered_samples(parameters, samples, extra_constraint):
    return dict((p,v) for (p,v) in samples.items() if not inside(parameters, p, extra_constraint))

parser = argparse.ArgumentParser(description='Use the models\' rational polynomial to synthesise its fulfilling parameter values.')
parser.add_argument('--file',  help='the input file containing the polynomial description of the system', required=True)
parser.add_argument('--threshold', type=float, help='property to be checked', default=0.5)
parser.add_argument('--samples', type=int, help='sample points in each dimension (default: 4)', default=4)
parser.add_argument('--display', help="graphs to be displayed ('all', 'bool', 'val'")
parser.add_argument('--precision', type=int, help="precision used for evaluation", default=20)
parser.add_argument('--constraints', help="method to be used for constraint generation", default="auto")
parser.add_argument('--iterations', type=int, help="number of iterations to be performed", default=4)
cmdargs = parser.parse_args()

threshold = vars(cmdargs)['threshold']
RationalFunction.evaluation_precision = vars(cmdargs)['precision']
nr_samples = vars(cmdargs)['samples']


# read comics output from file
[parameters, constraints, nominator, denominator] = get_polynomials_from_comics_file(vars(cmdargs)['file'])
name = os.path.splitext(os.path.basename(vars(cmdargs)['file']))[0]

samples = {}
safe = []
bad = []
excluded_regions = []
ratfunc = RationalFunction(nominator, denominator)

i = 0
bd = 0.1
while(i < vars(cmdargs)['iterations']):
    print("iteration %d / %d" % i, vars(cmdargs)['iterations'])
    if len(samples) == 0: 
        #evaluate rational function at specific points    
        for p in iterable_param.IterableParam(parameters,nr_samples, bound_distance=bd):
            evalVal = ratfunc.evaluate(p)
            point = tuple([value for [variable, value] in p])
            samples[point] = evalVal
        epsilon = (1-2*bd)/(nr_samples-1)
        delta = math.sqrt(2*(epsilon*epsilon) + epsilon/2)
        j = 0
        while j < 3:
            good_samples = [k for k,v in samples.items() if v > threshold]
            bad_samples = [k for k,v in samples.items() if v <= threshold]
            print(good_samples)
            print(bad_samples)
            print(delta)
            for gs in good_samples:
                for bs in bad_samples:
                    distance = math.hypot(gs[0]-bs[0], gs[1]-bs[1])
                    #print(str(gs) + " -- " + str(bs) + ": " + str(distance))   
                    if distance < delta:
                        p = tuple([(i_gs + i_bs)/2 for i_gs, i_bs in zip(gs,bs)])
                        samples[p] = ratfunc.evaluate(zip(parameters, p))
            j = j + 1
            delta = delta * 0.7
        print(samples)    
        # display
        if vars(cmdargs)['display'] == 'val' or  vars(cmdargs)['display'] == 'all':
            plot_results_val(parameters, samples)        
        if vars(cmdargs)['display'] == 'bool' or  vars(cmdargs)['display'] == 'all':
            plot_results_bool(parameters, dict([(p, v > threshold) for p,v in samples.items()]))    
    # export sample points.
    samplepoints_filepath = samplepoints_to_file(name, parameters, threshold, samples)

    # produce extra constraints
    if vars(cmdargs)['constraints'] == "manual":
        input("Edit constraints file and press Enter to continue...")
    else:
        generate_constraints(samplepoints_filepath, os.path.join(TMP_DIR,( name + "_" + str(i) + ".constraints")))
    # import constraints.
    safity, extra_constraints = constraints_from_file(os.path.join(TMP_DIR,( name + "_" + str(i) + ".constraints")), parameters)
    # export problem as smt2
    smt2_to_file(name, parameters, constraints + extra_constraints, nominator, denominator, threshold, excluded_regions, safity)
    # call smt solver
    (smtres, model) = call_smt_solver("z3", name)

    if smtres == "sat":
        modelPoint = tuple([model[p.name] for p in parameters])
        print(modelPoint)
        samples[modelPoint] = ratfunc.evaluate(list(model.items()))
        print(samples)
    else:
        samples = remove_covered_samples(parameters, samples, extra_constraints)
        if safity:
            safe.append(extra_constraints)
        else:
            bad.append(extra_constraints)
        excluded_regions.append(extra_constraints)    
        print(safe)
        print(bad)
    plot_constraints(parameters, safe, bad)        
        
    
    
    # display
    if vars(cmdargs)['display'] == 'val' or  vars(cmdargs)['display'] == 'all':
        plot_results_val(parameters, samples)        
    if vars(cmdargs)['display'] == 'bool' or  vars(cmdargs)['display'] == 'all':
        plot_results_bool(parameters, dict([(p, v > threshold) for p,v in samples.items()]))
    i = i + 1

    

