#!/usr/bin/env python3

"""Demonstrate usage of ShortestPathsGenerator API."""


import click
from stormpy.utility.utility import ShortestPathsGenerator

from prophesy.adapter.pycarl import convert_to_storm_type
from prophesy.data.constant import Constants
from prophesy.data.point import Point
from prophesy.input.modelfile import open_model_file
from prophesy.input.pctlfile import PctlFile
from prophesy.modelcheckers.stormpy import StormpyModelChecker
from scripts.modelrepair import parse_parameters


@click.command()
@click.option('--k', help='number of shortest paths to be generated', default=1000000)
@click.option('--target', help='target of shortest paths (label, state ID, or list of state IDs)', default='target')
@click.option('--prism-file', help='parametric Markov chain in Prism file format', type=click.Path(exists=True),
              default='../benchmarkfiles/brp/brp_16-2.pm', required=True)
@click.option('--pctl-file', help='PCTL property file containing property (e.g., P=? [F "target"])',
              type=click.Path(exists=True), default='../benchmarkfiles/brp/property1.pctl', required=True)
@click.option('--pctl-index', help='index (0-based) of property in PCTL file', default=0, show_default=True)
@click.option('--parameter-values', help='values for the model\'s parameters [enclosed in quotes, separated by space;'
              ' order is determined by Prism file]', default='0.72 0.61')
def find_shortest_paths(prism_file, pctl_file, pctl_index, parameter_values, k, target):
    """Use ShortestPathsGenerator to list the shortest paths in an MC.

    This script is not really intended for actual usage, but as a demo.
    Have a look at the source to see how to use Storm's
    ShortestPathsGenerator API.

    The paths are generated on-the-fly / incrementally.

    `get_states(k)` is accumulative, listing all states visited on the
    [1..k]-shortest paths.

    `get_path_as_list(k)` returns exactly the k-th shortest path.
    """
    def get_model_instance(prism_file_path, pctl_file_path, pctl_index, parameter_values_string):
        # this stuff is just preparation, not really relevant
        model_file = open_model_file(prism_file_path)
        parameter_values = [float(string) for string in parameter_values_string.split()]

        mc = StormpyModelChecker()
        mc.load_model(model_file)

        parameters = parse_parameters(model_file, Constants())

        pctl_property = PctlFile(pctl_file_path).get(pctl_index)
        mc.set_pctl_formula(pctl_property)

        # various representations / containers
        point = Point(*parameter_values).to_nice_rationals()
        parameter_instantiation = parameters.instantiate(point)

        mc.perform_sampling([parameter_instantiation])

        parameter_mapping = mc.get_parameter_mapping(parameter_instantiation.get_parameters())
        storm_parameter_mapping = {parameter_mapping[parameter]: convert_to_storm_type(val) for parameter, val in parameter_instantiation.items()}

        model_instantiator = mc.get_model_instantiator()
        instance = model_instantiator.instantiate(storm_parameter_mapping)

        return instance

    instance = get_model_instance(prism_file, pctl_file, pctl_index, parameter_values)

    spg = ShortestPathsGenerator(instance, target)  # TODO: get target label from parsed property

    states_in_k_shortest_paths = spg.get_states(k)
    print("States visit on the k shortest paths: ", states_in_k_shortest_paths)

    some_path = spg.get_path_as_list(k)
    print("As an example, here's the actual {}-shortest path: ".format(k), some_path)


if __name__ == "__main__":
    find_shortest_paths()
