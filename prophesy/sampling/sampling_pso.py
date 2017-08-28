import prophesy.adapter.pycarl as pc
from optimization.optimizers import ParticleSwarmOptimizer

from prophesy.data.point import Point
from prophesy.data.samples import ParameterInstantiations
from prophesy.sampling.sample_generator import SampleGenerator


def coords_to_rational_point(coords):
    return Point(*(pc.Rational(component) for component in coords))


class ParticleSwarmSampleGenerator(SampleGenerator):
    """Yields the particle positions for each PSO iteration."""
    # FIXME but thats wrong, should return sampling_result

    def __init__(self, sampler, parameters, score_fct, pso_options=None):
        super().__init__(sampler, parameters)
        self.score_fct = score_fct

        intervals = [p.interval for p in self.parameters]
        left_bounds = [float(i.left_bound()) for i in intervals]
        right_bounds = [float(i.right_bound()) for i in intervals]
        self.bounds = (left_bounds, right_bounds)

        if pso_options is None:
            pso_options = {'num_particles': 20, 'max_iters': 20}
        self._pso = ParticleSwarmOptimizer(self._objective, self.bounds, obj_fct_is_vectorized=True, options=pso_options)
        self._pso.initialize()

    def _objective(self, points):
        sampling_result = self._sample(points)
        return [self.score_fct(parameter_instantiation, value) for parameter_instantiation, value in sampling_result]

    def _sample(self, list_of_coords):
        rational_points = [coords_to_rational_point(coords) for coords in list_of_coords]
        parameter_instantiations = ParameterInstantiations.from_points(rational_points, self.parameters)
        results = self.sampler.perform_sampling(parameter_instantiations)
        return [(p, results[p]) for p in parameter_instantiations]

    def __iter__(self):
        yield self._pso.positions  # initial spawn
        while self._pso.stop():  # uh, yeah, I'll rename that
            self._pso.iteration += 1
            self._pso.iterate()
            yield self._pso.positions
        else:
            raise StopIteration
