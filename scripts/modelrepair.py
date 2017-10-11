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

Todo:
    * hint / subsys analysis
        * put ksp-SSG back
        * integrate full procedure
    * cost fct:
        * ask how to input exponents
        * ask if the unpacking can be handled gracefully
        * decide on what API is more convenient and clean (Parameters, Variables, Points, raw point?)
    * what's needed to handle MDPs?
"""

import copy

import click

import prophesy.adapter.pycarl as pc
from prophesy.config import configuration
from prophesy.data.constant import parse_constants_string
from prophesy.data.point import Point
from prophesy.data.samples import ParameterInstantiation
from prophesy.input.pctlfile import PctlFile
from prophesy.input.modelfile import open_model_file
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.modelrepair.repairer import ModelRepairer


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


# http://click.pocoo.org/5/parameters/#implementing-custom-types
class PolynomialParamType(click.ParamType):
    """Pycarl Polynomial CLI argument type for Click."""

    name = 'polynomial'

    def convert(self, value, param, ctx):
        """Try to parse with pycarl.parse()."""
        if value is None or value is '':
            return None
        try:
            possibly_not_polynomial = pc.parse(value)
            definitely_a_polynomial = pc.Polynomial(possibly_not_polynomial)
            return definitely_a_polynomial
        except pc.ParserError:
            self.fail('%s cannot be parsed as Pycarl polynomial' % value, param, ctx)


POLYNOMIAL_TYPE = PolynomialParamType()


@click.command()
@click.option('--prism-file', help='parametric Markov chain in Prism file format', type=click.Path(exists=True),
              default='../benchmarkfiles/brp/brp_16-2.pm', required=True, show_default=True)
@click.option('--pctl-file', help='PCTL property file containing property (e.g., P<=0.95 [F "target"])',
              type=click.Path(exists=True), default='../benchmarkfiles/brp/property_bound.pctl', required=True,
              show_default=True)
@click.option('--pctl-index', help='index (0-based) of property in PCTL file', default=0, show_default=True)
@click.option('--cost-function', help='polynomial cost function over the model\'s parameters in Pycarl prefix notation'
                                      ' (the default servers as demo, suitable for BRP)',
              type=POLYNOMIAL_TYPE, default='(+ (* (- pK 0.6) (- pK 0.6)) (* (- pL 0.7) (- pL 0.7)))',
              show_default=True)
@click.option('--modelchecker', type=click.Choice(MC_NAME_OPTIONS), default='stormpy', show_default=True)
@click.option('--constants', help='additional constants string over the model\'s parameters (rarely needed)')
@click.option('--hint', help='PSO hint (~ starting point), enclosed in quotes, separated by space,'
                             ' parameter order is determined by Prism file (e.g., "0.7 0.6")')
def model_repair(prism_file, pctl_file, pctl_index, cost_function, modelchecker, constants, hint):
    """Find low-cost parameter valuation satisfying the PCTL property.

    Given a parametric model and a PCTL property, a heuristic search
    tries to find the lowest-cost parameter valuation for which the
    property is satisfied.

    The cost function must be parseable by pycarl's parser. If it is
    omitted, the cost is not considered [but then this procedure makes
    little sense].

    NOTE: For demo purposes, the defaults currently show an example invocation
    (rather than being "sensible" for general usage).
    """
    prism_file = open_model_file(prism_file)
    mc = _get_selected_pmc(modelchecker)
    mc.load_model(prism_file)

    parameters = parse_parameters(prism_file, parse_constants_string(constants))
    parameters.make_intervals_closed(pc.Rational(pc.Integer(1), pc.Integer(1000)))

    pctl_property = PctlFile(pctl_file).get(pctl_index)

    if cost_function is None or cost_function is '':
        cost_function = pc.Polynomial(pc.parse("0"))

    if hint is not None:
        hint_as_floats = [float(string) for string in hint.split()]
        hint_as_param_inst = ParameterInstantiation.from_point(Point(*hint_as_floats).to_nice_rationals(), parameters)
    else:
        hint_as_param_inst = None

    repairer = ModelRepairer(mc, parameters, pctl_property, cost_fct=cost_function.evaluate, hint=hint_as_param_inst)
    result = repairer.repair()
    print(result)


if __name__ == "__main__":
    model_repair()