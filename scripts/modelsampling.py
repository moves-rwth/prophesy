#!/usr/bin/env python3


import sys
from argparse import ArgumentParser

from prophesy.input.prismfile import PrismFile
from prophesy.input.pctlfile import PctlFile
from prophesy.input.samplefile import write_samples_file
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.sampling.sampling import uniform_samples, refine_samples
from prophesy.adapter.pycarl import Rational


from prophesy.config import configuration

def parse_cli_args(args):
    parser = ArgumentParser(description='Perform sampling on a prism file')

    parser.add_argument('--file', help='the input file containing the prism file', required=True)
    parser.add_argument('--pctl-file', help='a file with a pctl property', required=True)
    parser.add_argument('--pctl-index', help='the index for the pctl file', default=0)
    parser.add_argument('--samples-file', help='resulting file', default="samples.out")
    parser.add_argument('--samplingnr', type=int, help='number of samples per dimension', default=4)
    parser.add_argument('--iterations', type=int, help='number of sampling refinement iterations', default=0)
    parser.add_argument('--threshold', type=float, help='the threshold', required=True)

    solver_group = parser.add_mutually_exclusive_group(required=True)
    solver_group.add_argument('--storm', action='store_true', help='use storm via cli')
    solver_group.add_argument('--prism', action='store_true', help='use prism via cli')
    solver_group.add_argument('--stormpy', action='store_true', help='use the storm via python API')

    return parser.parse_args(args)

def run(args = sys.argv, interactive=True):
    pmcs = configuration.getAvailableParametricMCs()
    cmdargs = parse_cli_args(args)

    prism_file = PrismFile(cmdargs.file)
    pctl_file = PctlFile(cmdargs.pctl_file)

    if cmdargs.storm:
        if 'storm' not in pmcs:
            raise RuntimeError("Storm location not configured.")
        tool = StormModelChecker()
    elif cmdargs.stormpy:
        if 'stormpy' not in pmcs:
            raise RuntimeError("Stormpy dependency not configured.")
        tool = StormpyModelChecker()
    elif cmdargs.prism:
        if 'prism' not in pmcs:
            raise RuntimeError("Prism location not configured.")
        tool = PrismModelChecker()
    else:
        raise RuntimeError("No supported model checker defined")

    tool.load_model_from_prismfile(prism_file)
    tool.set_pctl_formula(pctl_file.get(cmdargs.pctl_index))
    sampling_interface = tool
    cmdargs = parse_cli_args(args)

    parameters = prism_file.parameters
    parameters.make_intervals_closed(0.0001)

    initial_samples = uniform_samples(sampling_interface, parameters, cmdargs.samplingnr)
    print("Performing uniform sampling: {} samples".format(len(initial_samples)))

    refined_samples = refine_samples(sampling_interface, parameters, initial_samples, cmdargs.iterations,
                                     Rational(cmdargs.threshold))
    write_samples_file(result.parameters.get_variable_order(), refined_samples, cmdargs.samples_file)

    plot_path = plot_samples(refined_samples, parameters, cmdargs.safe_above_threshold, cmdargs.threshold)

if __name__ == "__main__":
   run()
