#!/usr/bin/env python3

"""Find parameter values that max- or minimize the value of a PCTL property."""

import copy

import click

import prophesy.adapter.pycarl as pc
from prophesy.config import configuration
from prophesy.data.constant import parse_constants_string
from prophesy.data.point import Point
from prophesy.data.property import Property
from prophesy.data.samples import ParameterInstantiation
from prophesy.input.modelfile import open_model_file
from prophesy.input.pctlfile import PctlFile
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.optimisation.heuristic_search import ModelOptimizer

MC_NAME_OPTIONS = ['stormpy', 'storm', 'prism']


def _get_selected_pmc(mc_name):
    """Return modelchecker instance for given name string."""
    assert mc_name in MC_NAME_OPTIONS

    configuration.check_tools()
    pmcs = configuration.getAvailableParametricMCs()
    if mc_name not in pmcs:
        raise RuntimeError("Model checker {} not configured!".format(mc_name))

    if mc_name == 'storm':
        return StormModelChecker()
    elif mc_name == 'stormpy':
        # Do not import at top, as stormpy might not be available.
        from prophesy.modelcheckers.stormpy import StormpyModelChecker
        return StormpyModelChecker()
    elif mc_name == 'prism':
        return PrismModelChecker()


def parse_parameters(prism_file, constants):
    """Return actual (i.e., non-constant) parameters."""
    parameters = copy.deepcopy(prism_file.parameters)
    for const_variable in constants.variables():
        parameters.remove_variable(const_variable)
    return parameters




@click.command()
@click.option('--direction', type=click.Choice(['min', 'max']), required=True)
@click.option('--prism-file', help='parametric Markov chain in Prism file format', type=click.Path(exists=True),
              required=True)
@click.option('--pctl-file', help='PCTL property file containing property (e.g., P=? [F "target"];'
                                  ' mutually exclusive with --pctl-string)', type=click.Path(exists=True))
@click.option('--pctl-index', help='index (0-based) of property in PCTL file', default=0, show_default=True)
@click.option('--pctl-string', help='direct entry of PCTL formula string (mutually exclusive with --pctl-file)')
@click.option('--modelchecker', type=click.Choice(MC_NAME_OPTIONS), default='stormpy', show_default=True)
@click.option('--constants', help='additional constants string over the model\'s parameters (rarely needed)')
def model_optimization(direction, prism_file, pctl_file, pctl_index, pctl_string, modelchecker, constants):
    """Find parameter valuations that {min,max}imize the property value.

    Given a parametric model and a PCTL property, a heuristic search
    tries to find the parameter valuation for which the property value is
    minimal respectively maximal.

    Example invocation:
    \b
    python optimize_model.py --prism-file ../benchmarkfiles/brp/brp_16-2.pm --pctl-string "P=? [F \"target\"]" --direction min
    """
    if not (pctl_file is not None) ^ bool(pctl_string):
        raise ValueError('PCTL property must be specified by file xor direct input.')

    prism_file = open_model_file(prism_file)
    mc = _get_selected_pmc(modelchecker)
    mc.load_model(prism_file)

    parameters = parse_parameters(prism_file, parse_constants_string(constants))
    parameters.make_intervals_closed(pc.Rational(pc.Integer(1), pc.Integer(1000000)))

    pctl_property = Property.from_string(pctl_string) if pctl_string else PctlFile(pctl_file).get(pctl_index)

    optimizer = ModelOptimizer(mc, parameters, pctl_property, direction)
    location, score = optimizer.search()
    result_as_instantiation = ParameterInstantiation.from_point(Point(*location), parameters)

    mc_result = score if direction == 'min' else -score
    print("Best location {} with property value {:.6f} \n".format(location, float(mc_result)))
    print("Parameter instantiation object: {}".format(result_as_instantiation))


if __name__ == "__main__":
    model_optimization()
