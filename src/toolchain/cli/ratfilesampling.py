#!/usr/bin/env python3

import sys
import os
# import library. Using this instead of appends prevents naming clashes..
thisfilepath = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))

import tempfile
import argparse
from input.resultfile import read_pstorm_result
from config import PLOT_FILES_DIR
from sampling.sampling import write_samples_file
from sampling.sampler_ratfunc import RatFuncSampling
from sampling.sampler_prism import McSampling
from sampling.sampling_linear import LinearRefinement
from sampling.sampling_delaunay import DelaunayRefinement
from sampling.sampling_uniform import UniformSampleGenerator
from output.plot import Plot

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = 'Perform sampling based on a rational function.')

    parser.add_argument('--rat-file', help = 'the input file containing the prism file', required = True)
    parser.add_argument('--samples-file', help = 'resulting file', default = "samples.out")
    parser.add_argument('--samplingnr', type = int, help = 'number of samples per dimension', default = 4)
    parser.add_argument('--iterations', type = int, help = 'number of sampling refinement iterations', default = 0)
    parser.add_argument('--threshold', type = float, help = 'the threshold', required = True)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--safe-above-threshold', action = 'store_true', dest = "safe_above_threshold")
    group.add_argument('--bad-above-threshold', action = 'store_false', dest = "safe_above_threshold")
    cmdargs = parser.parse_args()

    # Read previously generated result
    result = read_pstorm_result(cmdargs.rat_file)
    print("Parameters:", result.parameters)
    sampling_interface = RatFuncSampling(result.ratfunc, result.parameters)

    # Generate sample points (uniform grid)
    samples = {}
    intervals = [(0.01, 0.99)] * len(result.parameters)
    uniform_generator = UniformSampleGenerator(sampling_interface, intervals, cmdargs.samplingnr)
    for new_samples in uniform_generator:
        samples.update(new_samples)
    print("Performing uniform sampling: {} samples".format(len(samples)))

    # Refine the samples
    refinement_generator = LinearRefinement(sampling_interface, samples, cmdargs.threshold)
    refinement_generator = DelaunayRefinement(sampling_interface, samples, cmdargs.threshold)
    # Using range to limit the number of iterations
    for (new_samples,i) in zip(refinement_generator, range(0, cmdargs.iterations)):
        print("Refining sampling ({}/{}): {} new samples".format(i+1, cmdargs.iterations, len(new_samples)))
        samples.update(new_samples)

    # Dump the plot
    if not cmdargs.safe_above_threshold:
        Plot.flip_green_red = True
    (_, path_to_save) = tempfile.mkstemp(suffix = ".pdf", prefix = "sampling_", dir = PLOT_FILES_DIR)
    samples_green = [pt for pt, v in samples.items() if v >= cmdargs.threshold]
    samples_red = [pt for pt, v in samples.items() if v < cmdargs.threshold]
    Plot.plot_results(parameters=result.parameters, samples_green=samples_green, samples_red=samples_red,
                      path_to_save=path_to_save, display=False)
    print("Samples rendered to {}".format(path_to_save))
    write_samples_file([p.name for p in result.parameters], samples, cmdargs.threshold, cmdargs.samples_file)

    os.system("xdg-open {}".format(path_to_save))
