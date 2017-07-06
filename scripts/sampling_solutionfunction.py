#!/usr/bin/env python3

import sys
from argparse import ArgumentParser
import logging

from prophesy.output.plot import plot_samples
from prophesy.input.solutionfunctionfile import read_pstorm_result
from prophesy.input.samplefile import write_samples_file
from prophesy.sampling.sampling import uniform_samples,refine_samples
from prophesy.sampling.sampler_ratfunc import RatFuncSampling
from prophesy.util import open_file
from prophesy.adapter.pycarl import Rational
from prophesy.config import configuration


def _get_argparser():
    parser = ArgumentParser(description='Perform sampling based on a rational function.')

    parser.add_argument('--rat-file', help='the input file containing the prism file', required=True)
    parser.add_argument('--samples-file', help='resulting file', default="samples.out")
    parser.add_argument('--samplingnr', type=int, help='number of samples per dimension', default=4)
    parser.add_argument('--iterations', type=int, help='number of sampling refinement iterations', default=0)
    parser.add_argument('--threshold', type=float, help='the threshold', required=True)

    parser.add_argument('--bad-above-threshold', action='store_false', dest="safe_above_threshold", default=True)

    return parser


def parse_cli_args(args):
    """Parse and return command-line arguments."""
    return _get_argparser().parse_args(args)


def run(args=sys.argv[1:], interactive=True):
    cmdargs = parse_cli_args(args)
    configuration.check_tools()
    threshold = Rational(cmdargs.threshold)

    # Read previously generated result
    result = read_pstorm_result(cmdargs.rat_file)
    logging.debug("Parameters: %s", str(result.parameters))

    sampling_interface = RatFuncSampling(result.ratfunc, result.parameters)

    initial_samples = uniform_samples(sampling_interface, result.parameters, cmdargs.samplingnr)
    logging.info("Performing uniform sampling: {} samples".format(len(initial_samples)))

    refined_samples = refine_samples(sampling_interface, result.parameters, initial_samples, cmdargs.iterations,
                                     threshold)
    write_samples_file(result.parameters, refined_samples, cmdargs.samples_file)

    if len(result.parameters) <= 2:
        plot_path = plot_samples(refined_samples, result.parameters, cmdargs.safe_above_threshold, threshold)

        if interactive:
            open_file(plot_path)
    else:
        logging.info("Cannot plot, as dimension is too high!")


if __name__ == "__main__":
    run()
