#!/usr/bin/env python3

import tempfile
import sys
from argparse import ArgumentParser


from prophesy.output.plot import Plot
from prophesy.input.resultfile import read_pstorm_result
from prophesy.config import configuration
from prophesy.input.samplefile import write_samples_file
from prophesy.sampling.sampling import uniform_samples,refine_samples
from prophesy.sampling.sampler_ratfunc import RatFuncSampling
from prophesy.util import open_file


def parse_cli_args(args):
    """Parse and return command-line arguments."""
    parser = ArgumentParser(description='Perform sampling based on a rational function.')

    parser.add_argument('--rat-file', help='the input file containing the prism file', required=True)
    parser.add_argument('--samples-file', help='resulting file', default="samples.out")
    parser.add_argument('--samplingnr', type=int, help='number of samples per dimension', default=4)
    parser.add_argument('--iterations', type=int, help='number of sampling refinement iterations', default=0)
    parser.add_argument('--threshold', type=float, help='the threshold', required=True)

    parser.add_argument('--bad-above-threshold', action='store_false', dest="safe_above_threshold", default=True)

    return parser.parse_args(args)


def plot_samples(samples, parameters, safe_above_threshold, threshold):
    """Plot samples and return path to file."""
    if not safe_above_threshold:
        Plot.flip_green_red = True

    _, plot_path = tempfile.mkstemp(suffix=".pdf", prefix="sampling_", dir=configuration.get_plots_dir())

    samples_green = [pt for pt, v in samples.items() if v >= threshold]
    samples_red = [pt for pt, v in samples.items() if v < threshold]

    Plot.plot_results(parameters=parameters, samples_green=samples_green, samples_red=samples_red,
                      path_to_save=plot_path, display=False)
    print("Samples rendered to {}".format(plot_path))

    return plot_path


def run(args=sys.argv, interactive=True):
    cmdargs = parse_cli_args(args)

    # Read previously generated result
    result = read_pstorm_result(cmdargs.rat_file)
    print("Parameters:", result.parameters)

    sampling_interface = RatFuncSampling(result.ratfunc, result.parameters.get_variable_order())

    initial_samples = uniform_samples(sampling_interface, result.parameters, cmdargs.samplingnr)
    print("Performing uniform sampling: {} samples".format(len(initial_samples)))

    refined_samples = refine_samples(sampling_interface, result.parameters, initial_samples, cmdargs.iterations,
                                     cmdargs.threshold)
    write_samples_file(result.parameters.get_variable_order(), refined_samples, cmdargs.samples_file)

    plot_path = plot_samples(refined_samples, result.parameters, cmdargs.safe_above_threshold, cmdargs.threshold)
    if interactive:
        open_file(plot_path)


if __name__ == "__main__":
    run()