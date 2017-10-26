"""Model repair implementation using sampling.

Uses PSO as the 'sampling strategy' but could use other Samplers.
"""

import copy

import prophesy.adapter.pycarl as pc

from prophesy.data.property import OperatorBound
from prophesy.sampling.sampling_pso import ParticleSwarmSampleGenerator


def dummy_cost_function(*_, **__):
    """Return constant regardless of arguments."""
    return 0


class ModelRepairer:
    """Performs model repair using PSO.

    Optionally accepts a hint which serves as starting point; in this case
    the particles are spawned close to it (specifically a Gaussian
    distribution centered around that point).

    Args:
        modelchecker: MC instance with model already loaded
        parameters: parameters of the model as required by Sampler
        pctl_property: property with inequality bound to be satisfied
        cost_fct: function that accepts dict of Variable -> Rational
        hint: ParameterInstantiation to be used as starting point
    """

    def __init__(self, modelchecker, parameters, pctl_property, cost_fct=None, hint=None, pso_options=None):
        if pctl_property.bound.asks_for_exact_value():
            raise ValueError("Bound must be one of <, <=, >, >=.")

        # the original property specifies a bound, but the actual model
        # checking call is done with the "=?" operator to get the MC prob
        self.original_property = pctl_property
        self.modified_property = copy.copy(pctl_property)
        self.modified_property.bound = OperatorBound(pc.Relation.EQ)
        modelchecker.set_pctl_formula(self.modified_property)

        self.cost_fct = cost_fct if cost_fct is not None else dummy_cost_function

        self._pso_sample_gen = ParticleSwarmSampleGenerator(modelchecker, parameters, self.score, hint=hint,
                                                            pso_options=pso_options)

    def repair(self):
        """Run PSO and return best result."""
        for _ in self._pso_sample_gen:
            # we don't actually want to look at them, just let the PSO iterate
            pass

        argmin = self._pso_sample_gen.pso.historic_best_position
        minimum = self._pso_sample_gen.pso.historic_best_score
        return argmin, minimum

    def score(self, parameter_instantiation, value):
        """Calculate objective function value from MC result and cost.

        If the parameter instantiation satisfies the PCTL property's
        bound, the score is simply the cost.

        If not, the score is a very large penalty plus the (absolute)
        difference between the MC result and the bound.

        (Like cost and anything else to be optimized in this context,
        smaller values are better. That's pretty unintuitive when it
        comes to terms like 'high score' -- but it isn't any better
        when done the other way around.)
        """
        penalty = 10000

        def distance_to_bound(value, bound):
            return abs(value - bound.threshold)

        if self.original_property.bound.is_satisfied(value):
            # it is nice to be able to use carl Polynomials, but they evaluate
            # on Variable:Rational dicts, not ParameterInstantiation (!)
            # TODO: maybe subclass Parameter from pycarl.Variable
            instantiation_as_dict = {p.variable: v for p, v in parameter_instantiation.items()}
            return float(self.cost_fct(instantiation_as_dict))
        else:
            return float(distance_to_bound(value, self.original_property.bound) + penalty)
