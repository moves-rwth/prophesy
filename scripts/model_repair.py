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

import argparse
import copy
import sys

from optimization.optimizers import ParticleSwarmOptimizer

import prophesy.adapter.pycarl as pc
from prophesy.config import configuration
from prophesy.data.constant import parse_constants_string
from prophesy.data.point import Point
from prophesy.data.property import Property, OperatorBound, OperatorDirection
from prophesy.data.samples import ParameterInstantiations
from prophesy.input.pctlfile import PctlFile
from prophesy.input.prismfile import PrismFile
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.modelcheckers.storm import StormModelChecker


def _parse_cli_args(args):
    parser = argparse.ArgumentParser(prog="model_repair", description=__doc__.split('\n', 2)[1],
                                     epilog=''.join(__doc__.split('\n', 3)[2:]))

    parser.add_argument('--prism-file', help='parametric MC in Prism format', required=True)
    parser.add_argument('--pctl-file', help='PCTL property file', required=True)
    parser.add_argument('--pctl-index', help='index of PCTL property to be satisfied (if there are several)', default=0)
    parser.add_argument('--cost-function', type=str, help='cost function to be minimized', default=None)
    parser.add_argument('--constants', type=str, help=argparse.SUPPRESS)

    solver_group = parser.add_mutually_exclusive_group(required=True)
    solver_group.add_argument('--storm', action='store_true', help='use Storm via CLI')
    solver_group.add_argument('--prism', action='store_true', help='use Prism via CLI')
    solver_group.add_argument('--stormpy', action='store_true', help='use Storm via the stormpy Python API')

    return parser.parse_args(args)


def _get_selected_pmc(cmdargs):
    pmcs = configuration.getAvailableParametricMCs()
    if cmdargs.storm:
        if 'storm' not in pmcs:
            raise RuntimeError("Storm location not configured.")
        return StormModelChecker()
    elif cmdargs.stormpy:
        if 'stormpy' not in pmcs:
            raise RuntimeError("Stormpy dependency not configured.")
        # Do not import at top, as stormpy might not be available.
        from prophesy.modelcheckers.stormpy import StormpyModelChecker
        return StormpyModelChecker()
    elif cmdargs.prism:
        if 'prism' not in pmcs:
            raise RuntimeError("Prism location not configured.")
        return PrismModelChecker()
    else:
        raise RuntimeError("No supported model checker defined")


def run(args=sys.argv[1:]):
    """TODO."""
    cmdargs = _parse_cli_args(args)

    configuration.check_tools()
    tool = _get_selected_pmc(cmdargs)

    prism_file = PrismFile(cmdargs.prism_file)
    tool.load_model_from_prismfile(prism_file)

    pctl_file = PctlFile(cmdargs.pctl_file)
    pctl_property = pctl_file.get(cmdargs.pctl_index)

    # TODO: what's needed to handle MDPs?
    if pctl_property.bound.asks_for_exact_value():
        raise ValueError("Bound must be one of <, <=, >, >=.")
    # FIXME: document conversion / expected input
    original_property_with_bound = pctl_property
    modified_property = Property(pctl_property.operator, operator_direction=OperatorDirection.unspecified,
                                 bound=OperatorBound(pc.Relation.EQ), pathformula=pctl_property.pathformula,
                                 reward_name=None)


    tool.set_pctl_formula(modified_property)

    parameters = copy.deepcopy(prism_file.parameters)
    constants = parse_constants_string(cmdargs.constants)
    for const_variable in constants.variables():
        parameters.remove_variable(const_variable)
    parameters.make_intervals_closed(pc.Rational(pc.Integer(1), pc.Integer(1000)))

    def sample(points):
        rational_points = [Point(*(pc.Rational(c) for c in p)) for p in points]
        sample_points = ParameterInstantiations.from_points(rational_points, parameters)
        result = tool.perform_sampling(sample_points)
        assert len(result) == len(points)  # FIXME numerically identical particles
        return result

    def cost(params, value):
        if value <= original_property_with_bound.bound.threshold:  # FIXME use Relation
            return sum(params)  # FIXME
        else:
            return 1 - value + 5000  # FIXME

    def objective(points):
        sampling_result = sample(points)
        return [cost(list(param_assignment.values()), v) for param_assignment, v in sampling_result]

    bounds = ([float(p.interval._left_value) for p in parameters], [float(p.interval._right_value) for p in parameters])
    opts = {'num_particles': 20, 'max_iters': 100}
    pso = ParticleSwarmOptimizer(objective, bounds, obj_fct_is_vectorized=True, options=opts)

    pso.optimize()
    argmin = pso.swarm.positions[pso.swarm.current_best_index]
    minimum = pso.swarm.scores[pso.swarm.current_best_index]
    print(argmin, float(minimum))
    print(float([v for k, v in sample([argmin])][0]))


if __name__ == "__main__":
    run()
