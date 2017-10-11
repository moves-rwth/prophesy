#!/usr/bin/env python3

import sys
import logging
import copy
from argparse import ArgumentParser

import prophesy.adapter.pycarl as pc
from prophesy.data.constant import parse_constants_string
from prophesy.output.plot import plot_samples
from prophesy.input.modelfile import open_model_file
from prophesy.input.pctlfile import PctlFile
from prophesy.input.samplefile import write_samples_file
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.sampling.sampling import uniform_samples, refine_samples
from prophesy.adapter.pycarl import Rational
from prophesy.config import configuration
from prophesy.data.property import OperatorDirection


def _get_argparser():
    parser = ArgumentParser(prog="sampling_model", description='Perform sampling on a prism file')

    parser.add_argument('--file', help='the input file containing the prism file', required=True)
    parser.add_argument('--pctl-file', help='a file with a pctl property', required=True)
    parser.add_argument('--pctl-index', help='the index for the pctl file', default=0)
    parser.add_argument('--samples-file', help='resulting file', default="samples.out")
    parser.add_argument('--samplingnr', type=int, help='number of samples per dimension', default=4)
    parser.add_argument('--iterations', type=int, help='number of sampling refinement iterations', default=0)
    parser.add_argument('--threshold', type=Rational, help='the threshold', required=True)
    parser.add_argument('--bad-above-threshold', action='store_false', dest="safe_above_threshold", default=True)
    parser.add_argument('--constants', type=str, help='string with constants')

    solver_group = parser.add_mutually_exclusive_group(required=True)
    solver_group.add_argument('--storm', action='store_true', help='use storm via cli')
    solver_group.add_argument('--prism', action='store_true', help='use prism via cli')
    solver_group.add_argument('--stormpy', action='store_true', help='use the storm via python API')

    return parser


def parse_cli_args(args):
    return _get_argparser().parse_args(args)


def run(args=sys.argv[1:], interactive=True):
    pmcs = configuration.getAvailableParametricMCs()
    cmdargs = parse_cli_args(args)
    configuration.check_tools()
    threshold = Rational(cmdargs.threshold)
    constants = parse_constants_string(cmdargs.constants)

    model_file = open_model_file(cmdargs.file)
    pctl_file = PctlFile(cmdargs.pctl_file)

    if cmdargs.storm:
        if 'storm' not in pmcs:
            raise RuntimeError("Storm location not configured.")
        tool = StormModelChecker()
    elif cmdargs.stormpy:
        if 'stormpy' not in pmcs:
            raise RuntimeError("Stormpy dependency not configured.")
        # Do not import at top, as stormpy might not be available.
        from prophesy.modelcheckers.stormpy import StormpyModelChecker
        tool = StormpyModelChecker()
    elif cmdargs.prism:
        if 'prism' not in pmcs:
            raise RuntimeError("Prism location not configured.")
        tool = PrismModelChecker()
    else:
        raise RuntimeError("No supported model checker defined")

    tool.load_model(model_file, constants)
    property = pctl_file.get(cmdargs.pctl_index)
    if not property.bound.asks_for_exact_value():
        raise NotImplementedError("Only properties asking for the probability/reward '=?' are currently supported")
    if model_file.contains_nondeterministic_model():
        if property.operator_direction == OperatorDirection.unspecified:
            raise ValueError("For non-deterministic models, the operator direction should be specified.")
    tool.set_pctl_formula(property)
    sampling_interface = tool

    parameters = copy.deepcopy(model_file.parameters)
    for const_variable in constants.variables():
        parameters.remove_variable(const_variable)
    parameters.make_intervals_closed(pc.Rational(pc.Integer(1), pc.Integer(1000)))

    logging.info("Performing uniform sampling:")

    initial_samples = uniform_samples(sampling_interface, parameters, cmdargs.samplingnr)

    refined_samples = refine_samples(sampling_interface, parameters, initial_samples, cmdargs.iterations,
                                     threshold)
    write_samples_file(parameters, refined_samples, cmdargs.samples_file)

    if len(parameters) <= 2:
        plot_path = plot_samples(refined_samples, parameters, cmdargs.safe_above_threshold, threshold)
    else:
        logging.info("Cannot plot, as dimension is too high!")


if __name__ == "__main__":
    run()
