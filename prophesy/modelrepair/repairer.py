import copy

import prophesy.adapter.pycarl as pc

from prophesy.data.property import OperatorBound
from prophesy.sampling.sampling_pso import ParticleSwarmSampleGenerator


def dummy_cost_function(*_, **__):
    return 0


class ModelRepairer:
    def __init__(self, modelchecker, parameters, pctl_property, cost_fct=None, hint=None):
        # FIXME ensure modelchecker has model already loaded
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
        for _ in self.pso_sample_gen:
            # we don't actually want to look at them, just let the PSO iterate
            pass

        argmin = self.pso_sample_gen.pso.historic_best_position
        minimum = self.pso_sample_gen.pso.historic_best_score
        print(argmin, float(minimum))

    def score(self, parameter_instantiation, value):
        penalty = 10000

        def bound_is_satisfied(value, bound):
            assert bound.relation == pc.Relation.LEQ, "FIXME allow other relations"
            return value <= bound.threshold

        def distance_to_bound(value, bound):
            return abs(value - bound.threshold)

        if bound_is_satisfied(value, self.original_property.bound):
            return float(self.cost_fct(parameter_instantiation))
        else:
            return float(distance_to_bound(value, self.original_property.bound) + penalty)
