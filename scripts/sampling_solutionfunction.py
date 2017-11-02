#!/usr/bin/env python3

import sys
from argparse import ArgumentParser
import logging

from prophesy.output.plot import plot_samples
from prophesy.input.solutionfunctionfile import read_pstorm_result
from prophesy.input.samplefile import write_samples_file
from prophesy.sampling.sampling import uniform_samples, refine_samples

from prophesy.util import open_file
from prophesy.config import configuration
import prophesy.adapter.pycarl as pc



def _get_argparser():
    parser = ArgumentParser(description='Perform sampling based on a rational function.')

    parser.add_argument('--rat-file', help='the input file containing the prism file', required=True)
    parser.add_argument('--samples-file', help='resulting file', default="samples.out")

    parser.add_argument('--threshold', type=pc.Rational, help='the threshold', required=True)

    parser.add_argument('--bad-above-threshold', action='store_false', dest="safe_above_threshold", default=True)

    return parser


def parse_cli_args(args):
    """Parse and return command-line arguments."""
    return _get_argparser().parse_args(args)


def run(args=sys.argv[1:], interactive=True):
    cmdargs = parse_cli_args(args)
    configuration.check_tools()
    threshold = pc.Rational(cmdargs.threshold)

    # Read previously generated result
    result = read_pstorm_result(cmdargs.rat_file)
    logging.debug("Parameters: %s", str(result.parameters))



if __name__ == "__main__":
    run()
