import copy

import prophesy.adapter.pycarl as pc
from optimization.optimizers import ParticleSwarmOptimizer

from prophesy.data.point import Point
from prophesy.data.property import OperatorBound
from prophesy.data.samples import ParameterInstantiations


def coords_to_rational_point(coords):
    return Point(*(pc.Rational(component) for component in coords))


def dummy_cost_function(*_, **__):
    return 0


class ModelRepairer:
    def __init__(self, modelchecker, parameters, pctl_property, cost_fct=None):
        self.modelchecker = modelchecker  # with model already loaded, FIXME
        self.parameters = parameters
        self.pctl_property = pctl_property
        self.cost_fct = cost_fct if cost_fct is not None else dummy_cost_function

        if pctl_property.bound.asks_for_exact_value():
            raise ValueError("Bound must be one of <, <=, >, >=.")

        # the original property specifies a bound, but the actual model
        # checking call is done with the "=?" operator to get the MC prob
        self.modified_property = copy.deepcopy(pctl_property)
        self.modified_property.bound = OperatorBound(pc.Relation.EQ)
        self.modelchecker.set_pctl_formula(self.modified_property)

        intervals = [p.interval for p in self.parameters]
        left_bounds = [float(i.left_bound()) for i in intervals]
        right_bounds = [float(i.right_bound()) for i in intervals]
        self.bounds = (left_bounds, right_bounds)

        opts = {'num_particles': 20, 'max_iters': 50}
        self._optimizer = ParticleSwarmOptimizer(self._objective, self.bounds, obj_fct_is_vectorized=True, options=opts)

    def repair(self):
        self._optimizer.optimize()
        argmin = self._optimizer.historic_best_position
        minimum = self._optimizer.historic_best_score
        print(argmin, float(minimum))
        print(float([v for k, v in self._sample([argmin])][0]))

    def _objective(self, points):
        sampling_result = self._sample(points)
        return [self.score(parameter_instantiation, value) for parameter_instantiation, value in sampling_result]

    def _sample(self, list_of_coords):
        rational_points = [coords_to_rational_point(coords) for coords in list_of_coords]
        parameter_instantiations = ParameterInstantiations.from_points(rational_points, self.parameters)
        results = self.modelchecker.perform_sampling(parameter_instantiations)
        return [(p, results[p]) for p in parameter_instantiations]

    def score(self, parameter_instantiation, value):
        penalty = 10000

        def bound_is_satisfied(value, bound):
            assert bound.relation == pc.Relation.LEQ, "FIXME allow other relations"
            return value <= bound.threshold

        def distance_to_bound(value, bound):
            return abs(value - bound.threshold)

        if bound_is_satisfied(value, self.pctl_property.bound):
            return float(self.cost_fct(parameter_instantiation))
        else:
            return float(distance_to_bound(value, self.pctl_property.bound) + penalty)
