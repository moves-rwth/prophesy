#!/usr/bin/env python3

import os
import sys

# import library. Using this instead of appends prevents naming clashes..
this_file_path = os.path.dirname(os.path.realpath(__file__))
# insert at position 1; leave path[0] (directory at invocation) intact
sys.path.insert(1, os.path.join(this_file_path, '..'))

from argparse import ArgumentParser

from input.prismfile import PrismFile
from input.pctlfile import PctlFile
from input.samplefile import write_samples_file
from modelcheckers.prism import PrismModelChecker
from modelcheckers.storm import StormModelChecker
from sampling.sampler_prism import McSampling

import config
from config import configuration

def parse_cli_args():
    parser = ArgumentParser(description='Perform sampling on a prism file')

    parser.add_argument('--file', help='the input file containing the prism file', required=True)
    parser.add_argument('--pctl-file', help='a file with a pctl property', required=True)
    parser.add_argument('--pctl-index', help='the index for the pctl file', default=0)
    parser.add_argument('--samples-file', help='resulting file', default="samples.out")
    parser.add_argument('--samplingnr', type=int, help='number of samples per dimension', default=4)

    solver_group = parser.add_mutually_exclusive_group(required=True)
    solver_group.add_argument('--storm', action='store_true', help='use storm via cli')
    solver_group.add_argument('--prism', action='store_true', help='use prism via cli')
    solver_group.add_argument('--stormpy', action='store_true', help='use the python API')

    return parser.parse_args()


if __name__ == "__main__":
    pmcs = configuration.getAvailableParametricMCs()
    cmdargs = parse_cli_args()

    prism_file = PrismFile(cmdargs.file)
    pctl_file = PctlFile(cmdargs.pctl_file)

    if cmdargs.storm:
        if 'storm' not in  pmcs:
            raise RuntimeError("Storm location not configured.")
        tool = StormModelChecker()
    elif cmdargs.stormpy:
        if 'stormpy' not in  pmcs:
            raise RuntimeError("Stormpy dependency not configured.")
        tool = StormpyModelChecker()
    elif cmdargs.prism:
        if 'prism' not in  pmcs:
            raise RuntimeError("Prism location not configured.")
        tool = PrismModelChecker()
    else:
        raise RuntimeError("No supported model checker defined")

    intervals = [(0.01, 0.99)] * prism_file.nr_parameters()
    tool.load_model_from_prismfile(prism_file)
    tool.set_pctl_formula(pctl_file.get(cmdargs.pctl_index))
    sampling_interface = McSampling(tool)
    samples = sampling_interface.perform_uniform_sampling(intervals, cmdargs.samplingnr)
    # samples = perform_sampling_mc(tool, prism_file, vars(cmdargs)["pctl_file"], [(0.3, 0.3), (0.4, 0.4)])
    write_samples_file(prism_file.parameters, samples, cmdargs.samples_file)

