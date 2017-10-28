#!/usr/bin/env python3

"""Demonstrate usage of Stormpy instantiation & sampling API."""


import click

from prophesy.adapter.pycarl import convert_to_storm_type
from prophesy.data.constant import Constants
from prophesy.data.point import Point
from prophesy.input.pctlfile import PctlFile
from prophesy.input.modelfile import open_model_file
from prophesy.modelcheckers.stormpy import StormpyModelChecker
from scripts.modelrepair import parse_parameters


@click.command()
@click.option('--prism-file', help='parametric Markov chain in Prism file format', type=click.Path(exists=True),
              default='../benchmarkfiles/brp/brp_16-2.pm', required=True)
@click.option('--pctl-file', help='PCTL property file containing property (e.g., P=? [F "target"])',
              type=click.Path(exists=True), default='../benchmarkfiles/brp/property1.pctl', required=True)
@click.option('--pctl-index', help='index (0-based) of property in PCTL file', default=0, show_default=True)
@click.option('--parameter-values', help='values for the model\'s parameters [enclosed in quotes, separated by space;'
              ' order is determined by Prism file]', default='0.72 0.61')
def modelcheck(prism_file, pctl_file, pctl_index, parameter_values):
    """Use Stormpy to instantiate and modelcheck a parametric model.

    This script is not really intended for actual usage, but as a demo.
    Have a look at the source to see how to use the Stormpy API.
    """
    model_file = open_model_file(prism_file)
    parameter_values = [float(string) for string in parameter_values.split()]

    mc = StormpyModelChecker()
    mc.load_model(model_file)

    parameters = parse_parameters(model_file, Constants())

    pctl_property = PctlFile(pctl_file).get(pctl_index)
    mc.set_pctl_formula(pctl_property)

    point = Point(*parameter_values).to_nice_rationals()
    parameter_instantiation = parameters.instantiate(point)

    mc.perform_sampling([parameter_instantiation])

    # roughly same as stormpy.perform_sampling, but for single point
    def sample(parameter_instantiation):
        parameter_mapping = mc.get_parameter_mapping(parameter_instantiation.get_parameters())
        storm_parameter_mapping = {parameter_mapping[parameter]: convert_to_storm_type(val) for parameter, val in parameter_instantiation.items()}

        model_instantiator = mc.get_model_instantiator()
        instance = model_instantiator.instantiate(storm_parameter_mapping)

        rational_result = StormpyModelChecker.check_model(instance, mc.pctlformula[0])
        return rational_result

    result = sample(parameter_instantiation)
    print(float(result))


if __name__ == "__main__":
    modelcheck()
