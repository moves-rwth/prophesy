#!/usr/bin/env python3

import os
import sys

# import library. Using this instead of appends prevents naming clashes..
this_file_path = os.path.dirname(os.path.realpath(__file__))
# insert at position 1; leave path[0] (directory at invocation) intact
sys.path.insert(1, os.path.join(this_file_path, '../prophesy'))

from argparse import ArgumentParser

from input.prismfile import PrismFile
from modelcheckers.prism import PrismModelChecker
from sampling.sampler_prism import McSampling
from sampling.sampling import write_samples_file


def parse_cli_args():
    parser = ArgumentParser(description='Perform sampling on a prism file')

    parser.add_argument('--file', help='the input file containing the prism file', required=True)
    parser.add_argument('--pctl-file', help='a file with a pctl property', required=True)
    parser.add_argument('--samples-file', help='resulting file', default="samples.out")
    parser.add_argument('--samplingnr', type=int, help='number of samples per dimension', default=4)

    solver_group = parser.add_mutually_exclusive_group(required=True)
    solver_group.add_argument('--prism', help='the location of the prism binary')
    solver_group.add_argument('--storm', help='the location of the storm binary')

    return parser.parse_args()


if __name__ == "__main__":
    cmdargs = parse_cli_args()

    prism_file = PrismFile(cmdargs.file)

    if cmdargs.prism is not None:
        tool = PrismModelChecker(cmdargs.prism)
    elif cmdargs.storm != None:
        tool = StormModelChecker(cmdargs.storm)
    else:
        raise RuntimeError("No supported solver available")

    print("Perform sampling using " + tool.version())


    intervals = [(0.01, 0.99)] * prism_file.nr_parameters()
    sampling_interface = McSampling(tool, prism_file, cmdargs.pctl_file)
    samples = sampling_interface.perform_uniform_sampling(intervals, cmdargs.samplingnr)
    # samples = perform_sampling_mc(tool, prism_file, vars(cmdargs)["pctl_file"], [(0.3, 0.3), (0.4, 0.4)])
    write_samples_file(prism_file.parameters, samples, cmdargs.threshold, cmdargs.samples_file)
