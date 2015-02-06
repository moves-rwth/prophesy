#!/usr/bin/env python3

import sys
import os
# import library. Using this instead of appends prevents naming clashes..
thisfilepath = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))

import argparse
import sampling
from input.resultfile import read_pstorm_result
from output.plot import Plot
import tempfile
from config import PLOT_FILES_DIR
from sampling import refine_sampling

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = 'Perform sampling based on a rational function.')

    parser.add_argument('--rat-file', help = 'the input file containing the prism file', required = True)
    parser.add_argument('--samples-file', help = 'resulting file', default = "samples.out")
    parser.add_argument('--samplingnr', type = int, help = 'number of samples per dimension', default = 4)
    parser.add_argument('--iterations', type = int, help = 'number of sampling refinement iterations', default = 0)
    parser.add_argument('--threshold', type = float, help = 'the threshold', required = True)
    group = parser.add_mutually_exclusive_group(required = True)
    group.add_argument('--safe-above-threshold', action = 'store_true', dest = "safe_above_threshold")
    group.add_argument('--bad-above-threshold', action = 'store_false', dest = "safe_above_threshold")
    cmdargs = parser.parse_args()

    # Read previously generated result
    result = read_pstorm_result(vars(cmdargs)['rat_file'])
    print("Parameters:", result.parameters)
    # Generate sample points (uniform grid)
    intervals = [(0.01, 0.99)] * len(result.parameters)
    sampling_interface = sampling.RatFuncSampling(result.ratfunc, result.parameters)
    # Calculate probabilities at sample points, and write to disk
    samples = sampling_interface.perform_uniform_sampling(intervals, vars(cmdargs)['samplingnr'])
    filter = False
    for _ in range(0, cmdargs.iterations):
        new_samples = refine_sampling(samples, cmdargs.threshold, sampling_interface, cmdargs.safe_above_threshold, filter)
        filter = False
        samples.update(new_samples)
    (_, path_to_save) = tempfile.mkstemp(suffix = ".pdf", prefix = "sampling_", dir = PLOT_FILES_DIR)
    plot_samples = {k:((v >= cmdargs.threshold) == cmdargs.safe_above_threshold) for k,v in samples.items()}
    Plot.plot_results(parameters=result.parameters, samples_qualitative=plot_samples,
                      path_to_save=path_to_save, display=False)
    print("Samples rendered to {}".format(path_to_save))
    # samples = sampling.perform_sampling_by_rf(ratfunc, parameters, [(0.3, 0.3), (0.4, 0.4)])
    sampling.write_samples_file([p.name for p in result.parameters], samples, vars(cmdargs)["samples_file"])

    os.system("xdg-open {}".format(path_to_save))
