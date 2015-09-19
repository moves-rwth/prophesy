#!/usr/bin/env python3

import sys
import os

# import library. Using this instead of appends prevents naming clashes..
this_file_path = os.path.dirname(os.path.realpath(__file__))
# insert at position 1; leave path[0] (directory at invocation) intact
sys.path.insert(1, os.path.join(this_file_path, '../prophesy'))

import platform
import tempfile
import argparse

from input.resultfile import read_pstorm_result
from config import PLOT_FILES_DIR
from sampling.sampling import write_samples_file
from sampling.sampler_ratfunc import RatFuncSampling
# from sampling.sampler_prism import McSampling # unused
# from sampling.sampler_carl import CarlSampling # needs fix
# from sampling.sampling_linear import LinearRefinement # unused
from sampling.sampling_delaunay import DelaunayRefinement
from sampling.sampling_uniform import UniformSampleGenerator
from output.plot import Plot


def parse_cli_args():
    """Parse and return command-line arguments."""
    parser = argparse.ArgumentParser(description='Perform sampling based on a rational function.')

    parser.add_argument('--rat-file', help='the input file containing the prism file', required=True)
    parser.add_argument('--samples-file', help='resulting file', default="samples.out")
    parser.add_argument('--samplingnr', type=int, help='number of samples per dimension', default=4)
    parser.add_argument('--iterations', type=int, help='number of sampling refinement iterations', default=0)
    parser.add_argument('--threshold', type=float, help='the threshold', required=True)

    group = parser.add_mutually_exclusive_group()
    group.add_argument('--safe-above-threshold', action='store_true', dest="safe_above_threshold")
    group.add_argument('--bad-above-threshold', action='store_false', dest="safe_above_threshold")

    return parser.parse_args()


def uniform_samples(interface, dimensions, samples_per_dim):
    """Generate a uniform grid of samples."""
    samples = {}
    intervals = [(0.01, 0.99)] * dimensions
    uniform_generator = UniformSampleGenerator(interface, intervals, samples_per_dim)

    for new_samples in uniform_generator:
        samples.update(new_samples)

    print("Performing uniform sampling: {} samples".format(len(samples)))
    return samples


def refine_samples(interface, samples, iterations, threshold, safe_above_threshold):
    """Refine samples over several iterations."""
    # refinement_generator = LinearRefinement(interface, samples, threshold)
    refinement_generator = DelaunayRefinement(interface, samples, threshold)

    # Using range to limit the number of iterations
    for (new_samples, i) in zip(refinement_generator, range(0, iterations)):

        # uncomment to see intermediate plot before each iteration
        # open_file(plot_samples(samples, result.parameters, safe_above_threshold, threshold))

        print("Refining sampling ({}/{}): {} new samples".format(i + 1, iterations, len(new_samples)))
        samples.update(new_samples)

    return samples


def plot_samples(samples, parameters, safe_above_threshold, threshold):
    """Plot samples and return path to file."""
    Plot.flip_green_red = True if not safe_above_threshold else False

    _, plot_path = tempfile.mkstemp(suffix=".pdf", prefix="sampling_", dir=PLOT_FILES_DIR)

    samples_green = [pt for pt, v in samples.items() if v >= threshold]
    samples_red = [pt for pt, v in samples.items() if v < threshold]

    Plot.plot_results(parameters=parameters, samples_green=samples_green, samples_red=samples_red,
                      path_to_save=plot_path, display=False)
    print("Samples rendered to {}".format(plot_path))

    return plot_path


def open_file(path):
    """Open file with system-default application.

    Works for Mac OS (`open`) and Linux with `xdg-open`."""
    platform_specific_open = 'open' if platform.system() == 'Darwin' else 'xdg-open'
    os.system("{open_cmd} {file}".format(open_cmd=platform_specific_open, file=path))


if __name__ == "__main__":
    cmdargs = parse_cli_args()

    # Read previously generated result
    result = read_pstorm_result(cmdargs.rat_file)
    print("Parameters:", result.parameters)

    sampling_interface = RatFuncSampling(result.ratfunc, result.parameters, False)
    # sampling_interface = CarlSampling(result.ratfunc, result.parameters)

    initial_samples = uniform_samples(sampling_interface, len(result.parameters), cmdargs.samplingnr)

    refined_samples = refine_samples(sampling_interface, initial_samples, cmdargs.iterations, cmdargs.threshold, cmdargs.safe_above_threshold)

    write_samples_file([p.name for p in result.parameters], refined_samples, cmdargs.threshold, cmdargs.samples_file)

    plot_path = plot_samples(refined_samples, result.parameters, cmdargs.safe_above_threshold, cmdargs.threshold)
    open_file(plot_path)
