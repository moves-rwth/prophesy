#!/usr/bin/env python3

"""
Find feasible, low-cost parameter values.

Given a parametric Markov chain and a PCTL property, model repair
finds parameter valuations for which the MC satisfies the property
(called 'repairs'), while attempting to minimize a cost function
over the parameters (e.g., distance from some origin).

(The cost function may be omitted, but that's not very interesting.)

If a cost threshold is specified, the procedure terminates as soon
as it finds a repair that is at most this expensive. Otherwise, the
procedure continues until some internal termination criterion is
met.
"""

import copy

import click

import prophesy.adapter.pycarl as pc
from prophesy.config import configuration
from prophesy.data.constant import parse_constants_string
from prophesy.data.point import Point
from prophesy.data.samples import ParameterInstantiation
from prophesy.input.pctlfile import PctlFile
from prophesy.input.prismfile import PrismFile
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.model_repair.repairer import ModelRepairer


mc_name_options = ['stormpy', 'storm', 'prism']


def _get_selected_pmc(mc_name):
    assert mc_name in mc_name_options

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
    parameters = copy.deepcopy(prism_file.parameters)
    for const_variable in constants.variables():
        parameters.remove_variable(const_variable)
    return parameters


# TODO:
# * cost function (as string? as parsed by sympy or something?)
#    * pycarl parser (prefix notation, see SMT lib solutionfunctionfile)
# * what's needed to handle MDPs?
# * hint / subsys analysis
# * publish optim

@click.command()
@click.option('--prism-file', help='parametric Markov chain in Prism file format', type=click.Path(exists=True),
              default='../benchmarkfiles/brp/brp_16-2.pm', required=True)
@click.option('--pctl-file', help='PCTL property file containing property (e.g., P<=0.95 [F "target"])',
              type=click.Path(exists=True), default='../benchmarkfiles/brp/property_bound.pctl', required=True)
@click.option('--pctl-index', help='index (0-based) of property in PCTL file', default=0, show_default=True)
@click.option('--modelchecker', type=click.Choice(mc_name_options), default='stormpy', show_default=True)
@click.option('--constants', help='additional constants string for the MC (rarely needed)', required=False)
def model_repair(prism_file, pctl_file, pctl_index, modelchecker, constants):
    prism_file = PrismFile(prism_file)
    mc = _get_selected_pmc(modelchecker)
    mc.load_model_from_prismfile(prism_file)

    parameters = parse_parameters(prism_file, parse_constants_string(constants))
    parameters.make_intervals_closed(pc.Rational(pc.Integer(1), pc.Integer(1000)))

    pctl_property = PctlFile(pctl_file).get(pctl_index)

    def cost_function(parameter_instantiation):
        origin = ParameterInstantiation.from_point(Point(0.6, 0.7), parameters)
        return origin.numerical_distance(parameter_instantiation)

    mr = ModelRepairer(mc, parameters, pctl_property, cost_function)
    mr.repair()


if __name__ == "__main__":
    model_repair()
