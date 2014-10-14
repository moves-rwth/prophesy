#!/usr/bin/env python3

"""

"""
import sys
import os
# import library. Using this instead of appends prevents naming clashes..
thisfilepath =  os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))


import argparse

import util
import sampling
import constraint_generation
from input.resultfile import *

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Build constraints based on a sample file')
    
    safe_above_threshold = False
    parser.add_argument('--samples-file', help='file containing the sample points')
    parser.add_argument('--constraint-file', help='the file in which the constraints are stored')
    parser.add_argument('--threshold', type=float, help='the threshold', required=True)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--safe-above-threshold', action='store_true')
    group.add_argument('--bad-above-threshold', action='store_false', dest="safe-above-threshold")
    cmdargs = parser.parse_args()
    
    (samples, parameters) = sampling.parse_samples_file(vars(cmdargs)["samples_file"])
    print(samples)
    constraint_generation.create_halfspace_constraint(samples, vars(cmdargs)["threshold"], safe_above_threshold)
    