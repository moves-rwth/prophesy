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
from modelcheckers.storm import StormModelChecker
from sampling.sampler_prism import McSampling
from sampling.sampling import write_samples_file

import config
from config import configuration

def parse_cli_args(pmcs):
    parser = ArgumentParser(description='Perform sampling on a prism file')

    parser.add_argument('--file', help='the input file containing the prism file', required=True)
    parser.add_argument('--pctl-file', help='a file with a pctl property', required=True)
    parser.add_argument('--samples-file', help='resulting file', default="samples.out")
    parser.add_argument('--samplingnr', type=int, help='number of samples per dimension', default=4)

    solver_group = parser.add_mutually_exclusive_group(required=not pmcs)
    solver_group.add_argument('--prism', help='the location of the prism binary')
    solver_group.add_argument('--storm', help='the location of the storm binary')

    return parser.parse_args()


if __name__ == "__main__":
    pmcs = configuration.getAvailableParametricMCs()
    cmdargs = parse_cli_args(pmcs)

    prism_file = PrismFile(cmdargs.file)

    if cmdargs.prism is not None:
        tool = PrismModelChecker(cmdargs.prism)
    elif cmdargs.storm is not None:
        tool = StormModelChecker(cmdargs.storm)
    elif 'pstorm' in pmcs:
        tool = StormModelChecker(configuration.get(config.EXTERNAL_TOOLS, "storm"))
    elif 'prism' in pmcs:
        tool = PrismModelChecker(configuration.get(config.EXTERNAL_TOOLS, "prism"))
    else:
        raise RuntimeError("No supported model checker defined")

    print("Perform sampling using " + tool.version())


    intervals = [(0.01, 0.99)] * prism_file.nr_parameters()
    sampling_interface = McSampling(tool, prism_file, cmdargs.pctl_file)
    samples = sampling_interface.perform_uniform_sampling(intervals, cmdargs.samplingnr)
    # samples = perform_sampling_mc(tool, prism_file, vars(cmdargs)["pctl_file"], [(0.3, 0.3), (0.4, 0.4)])
    write_samples_file(prism_file.parameters, samples, cmdargs.threshold, cmdargs.samples_file)

