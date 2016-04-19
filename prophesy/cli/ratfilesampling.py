#!/usr/bin/env python3

import sys
import os

# import library. Using this instead of appends prevents naming clashes..
this_file_path = os.path.dirname(os.path.realpath(__file__))
# insert at position 1; leave path[0] (directory at invocation) intact
sys.path.insert(1, os.path.join(this_file_path, '..'))

import tempfile
from argparse import ArgumentParser

# from sampling.sampler_carl import CarlSampling # needs fix
# from sampling.sampling_linear import LinearRefinement # unused

from prophesy.output.plot import Plot
from prophesy.input.resultfile import read_pstorm_result
from prophesy import config
from prophesy.input.samplefile import write_samples_file
from prophesy.sampling.sampling import uniform_samples,refine_samples
from prophesy.sampling.sampler_ratfunc import RatFuncSampling
from prophesy.util import open_file


def parse_cli_args():
    """Parse and return command-line arguments."""
    parser = ArgumentParser(description='Perform sampling based on a rational function.')

    parser.add_argument('--rat-file', help='the input file containing the prism file', required=True)
    parser.add_argument('--samples-file', help='resulting file', default="samples.out")
    parser.add_argument('--samplingnr', type=int, help='number of samples per dimension', default=4)
    parser.add_argument('--iterations', type=int, help='number of sampling refinement iterations', default=0)
    parser.add_argument('--threshold', type=float, help='the threshold', required=True)

    group = parser.add_mutually_exclusive_group()
    group.add_argument('--safe-above-threshold', action='store_true', dest="safe_above_threshold")
    group.add_argument('--bad-above-threshold', action='store_false', dest="safe_above_threshold")

    return parser.parse_args()




def plot_samples(samples, parameters, safe_above_threshold, threshold):
    """Plot samples and return path to file."""
    Plot.flip_green_red = True if not safe_above_threshold else False

    _, plot_path = tempfile.mkstemp(suffix=".pdf", prefix="sampling_", dir=config.PLOTS)

    samples_green = [pt for pt, v in samples.items() if v >= threshold]
    samples_red = [pt for pt, v in samples.items() if v < threshold]

    Plot.plot_results(parameters=parameters, samples_green=samples_green, samples_red=samples_red,
                      path_to_save=plot_path, display=False)
    print("Samples rendered to {}".format(plot_path))

    return plot_path


if __name__ == "__main__":
    cmdargs = parse_cli_args()

    # Read previously generated result
    result = read_pstorm_result(cmdargs.rat_file)
    print("Parameters:", result.parameters)

    sampling_interface = RatFuncSampling(result.ratfunc, result.parameters)
    # sampling_interface = CarlSampling(result.ratfunc, result.parameters)

    initial_samples = uniform_samples(sampling_interface, result.parameters, cmdargs.samplingnr)
    print("Performing uniform sampling: {} samples".format(len(initial_samples)))

    refined_samples = refine_samples(sampling_interface, result.parameters, initial_samples, cmdargs.iterations, cmdargs.threshold)

    write_samples_file(result.parameters.get_variable_order(), refined_samples, cmdargs.samples_file)

    plot_path = plot_samples(refined_samples, result.parameters, cmdargs.safe_above_threshold, cmdargs.threshold)
    open_file(plot_path)
