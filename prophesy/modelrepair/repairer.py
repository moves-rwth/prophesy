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

    Optionally accepts a hint which serves as starting point.

    Args:
        modelchecker: MC instance with model already loaded (!) [FIXME]
        parameters: parameters of the model as required by Sampler
        pctl_property: property with inequality bound to be satisfied
        cost_fct: [FIXME cost fct API]
        hint: [FIXME e.g. [0.7, 0.6] -- should this be a Point?]
    """

    def __init__(self, modelchecker, parameters, pctl_property, cost_fct=None, hint=None):
        # FIXME ensure modelchecker has model already loaded
        # actually, I can rewrite this, this is no longer required
        if pctl_property.bound.asks_for_exact_value():
            raise ValueError("Bound must be one of <, <=, >, >=.")

        # the original property specifies a bound, but the actual model
        # checking call is done with the "=?" operator to get the MC prob
        self.original_property = pctl_property
        self.modified_property = copy.deepcopy(pctl_property)
        self.modified_property.bound = OperatorBound(pc.Relation.EQ)
        modelchecker.set_pctl_formula(self.modified_property)

        self.cost_fct = cost_fct if cost_fct is not None else dummy_cost_function

        self.pso_sample_gen = ParticleSwarmSampleGenerator(modelchecker, parameters, self.score, hint=hint)

    def repair(self):
        """Run PSO and return best result."""
        for _ in self.pso_sample_gen:
            # we don't actually want to look at them, just let the PSO iterate
            pass

        argmin = self.pso_sample_gen.pso.historic_best_position
        minimum = self.pso_sample_gen.pso.historic_best_score
        print(argmin, float(minimum))
        # FIXME actually return that stuff?? then I can hide pso, too

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

        def bound_is_satisfied(value, bound):
            assert bound.relation == pc.Relation.LEQ, "FIXME allow other relations"
            return value <= bound.threshold

        def distance_to_bound(value, bound):
            return abs(value - bound.threshold)

        if bound_is_satisfied(value, self.original_property.bound):
            return float(self.cost_fct(parameter_instantiation))  # FIXME cost fct API
        else:
            return float(distance_to_bound(value, self.original_property.bound) + penalty)
