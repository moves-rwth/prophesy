import copy

import prophesy.adapter.pycarl as pc
from optimization.optimizers import ParticleSwarmOptimizer

from prophesy.data.point import Point
from prophesy.data.property import OperatorBound
from prophesy.data.samples import ParameterInstantiations


def coords_to_rational_point(coords):
    return Point(*(pc.Rational(component) for component in coords))


class ModelRepairer:
    def __init__(self, modelchecker, parameters, pctl_property, cost_fct):
        self.modelchecker = modelchecker  # with model already loaded, FIXME
        self.parameters = parameters
        self.pctl_property = pctl_property
        self.cost_fct = cost_fct if cost_fct is not None else lambda *args, **kwargs: 0

        if pctl_property.bound.asks_for_exact_value():
            raise ValueError("Bound must be one of <, <=, >, >=.")

        # the original property specifies a bound, but the actual model
        # checking call is done with the "=?" operator to get the MC prob
        self.modified_property = copy.deepcopy(pctl_property)
        self.modified_property.bound = OperatorBound(pc.Relation.EQ)
        self.modelchecker.set_pctl_formula(self.modified_property)

        # FIXME
        self.bounds = ([float(p.interval._left_value) for p in parameters], [float(p.interval._right_value) for p in parameters])

        opts = {'num_particles': 20, 'max_iters': 50}
        self._pso = ParticleSwarmOptimizer(self._objective, self.bounds, obj_fct_is_vectorized=True, options=opts)

    def repair(self):
        self._pso.optimize()
        # FIXME API should hide swarm
        argmin = self._pso.swarm.positions[self._pso.swarm.current_best_index]
        minimum = self._pso.swarm.scores[self._pso.swarm.current_best_index]
        print(argmin, float(minimum))
        print(float([v for k, v in self._sample([argmin])][0]))

    def _objective(self, points):
        sampling_result = self._sample(points)
        return [self.score(k.get_point(self.parameters), v) for k, v in sampling_result]

    def _sample(self, list_of_coords):
        rational_points = [coords_to_rational_point(coords) for coords in list_of_coords]
        sample_points = ParameterInstantiations.from_points(rational_points, self.parameters)
        result = self.modelchecker.perform_sampling(sample_points)

        assert len(result) == len(list_of_coords)  # FIXME numerically identical particles
        return result

    def score(self, point, value):
        penalty = 10000

        def bound_is_satisfied(value, bound):
            assert bound.relation == pc.Relation.LEQ, "FIXME allow other relations"
            return value <= bound.threshold

        def distance_to_bound(value, bound):
            return abs(value - bound.threshold)

        if bound_is_satisfied(value, self.pctl_property.bound):
            return self.cost_fct(point)
        else:
            return distance_to_bound(value, self.pctl_property.bound) + penalty
