import prophesy.adapter.pycarl as pc
from heuristic_optimization.optimizers import ParticleSwarmOptimizer
from heuristic_optimization.util.position_initializers import clamped_gaussian_distribution

from prophesy.data.point import Point
from prophesy.data.samples import ParameterInstantiations
from prophesy.sampling.sample_generator import SampleGenerator


def coords_to_rational_point(coords):
    return Point(*(pc.Rational(component) for component in coords))


class GuidedParticleSwarmOptimizer(ParticleSwarmOptimizer):
    def _generate_initial_positions(self):
        return clamped_gaussian_distribution(self.options['num_particles'], mean_point=self.options['hint'],
                                             bounds=(self.lower_bound, self.upper_bound),
                                             standard_deviation=0.1)  # FIXME: check if that number is reasonable
        # ... actually that should depend on the size of the search space, so maybe it should actually be based on that


class ParticleSwarmSampleGenerator(SampleGenerator):
    """Perform PSO yielding each iterations' samples (particle positions)."""

    def __init__(self, sampler, parameters, score_fct, hint=None, pso_options=None):
        super().__init__(sampler, parameters)
        self.score_fct = score_fct
        self.latest_sampling_result = None

        intervals = [p.interval for p in self.parameters]
        left_bounds = [float(i.left_bound()) for i in intervals]
        right_bounds = [float(i.right_bound()) for i in intervals]
        self.bounds = (left_bounds, right_bounds)

        if pso_options is None:
            pso_options = {'num_particles': 20, 'max_iters': 20}
        pso_options['hint'] = hint

        PSO = GuidedParticleSwarmOptimizer if hint is not None else ParticleSwarmOptimizer

        self.pso = PSO(self._objective, self.bounds, obj_fct_is_vectorized=True, options=pso_options)
        self.pso.initialize()

    def _objective(self, list_of_coords):
        rational_points = [coords_to_rational_point(coords) for coords in list_of_coords]
        parameter_instantiations = ParameterInstantiations.from_points(rational_points, self.parameters)

        results = self.sampler.perform_sampling(parameter_instantiations)
        self.latest_sampling_result = results

        result_as_ordered_list = [(p, results[p]) for p in parameter_instantiations]
        return [self.score_fct(param_inst, value) for param_inst, value in result_as_ordered_list]

    def __iter__(self):
        """Does what IterativeOptimizer.optimize does but yields stuff."""
        yield self.latest_sampling_result  # initial spawn
        while not self.pso.stop():
            self.pso.iteration += 1
            self.pso.iterate()
            yield self.latest_sampling_result
        else:
            raise StopIteration
