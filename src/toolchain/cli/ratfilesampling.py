#!/usr/bin/env python3

import sys
import os
# import library. Using this instead of appends prevents naming clashes..
thisfilepath = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))

import argparse
import sampling
from input.resultfile import read_pstorm_result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = 'Perform sampling based on a rational function.')

    parser.add_argument('--rat-file', help = 'the input file containing the prism file', required = True)
    parser.add_argument('--samples-file', help = 'resulting file', default = "samples.out")
    parser.add_argument('--samplingnr', type = int, help = 'number of samples per dimension', default = 4)
    cmdargs = parser.parse_args()


    result = read_pstorm_result(vars(cmdargs)['rat_file'])
    intervals = [(0.01, 0.99)] * len(result.parameters)
    sampling_interface = sampling.RatFuncSampling(result.ratfunc, result.parameters)
    print(result.parameters)
    samples = sampling_interface.perform_uniform_sampling(intervals, vars(cmdargs)['samplingnr'])
    print(samples)

    # samples = sampling.perform_sampling_by_rf(ratfunc, parameters, [(0.3, 0.3), (0.4, 0.4)])
    sampling.write_samples_file([p.name for p in result.parameters], samples, vars(cmdargs)["samples_file"])
