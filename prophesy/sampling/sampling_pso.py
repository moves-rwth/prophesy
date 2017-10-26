"""Wraps PSO so that it conforms to the sample generator API.

This means that the particle swarm is treated as a generator which
internally performs the PSO iteration then yields the particles'
positions / values as sampling result. When the PSO terminates,
the generator is exhausted.

Unfortunately this means that all this is essentially glue code.
"""

from collections import namedtuple

import prophesy.adapter.pycarl as pc
from prophesy.data.point import Point
from prophesy.sampling.sample_generator import SampleGenerator

from heuristic_optimization.optimizers import ParticleSwarmOptimizer
from heuristic_optimization.util.position_initializers import clamped_gaussian_distribution


def _coords_to_rational_point(coords):
    return Point(*(pc.Rational(component) for component in coords))


class EarlyTerminatingParticleSwarmOptimizer(ParticleSwarmOptimizer):
    """PSO that terminates early if the best score stagnates.

    Easily extensible to cover other termination conditions.
    """

    HistoryEntry = namedtuple('HistoryEntry', ['iteration', 'score', 'position'])

    def __init__(self, objective_function, bounds, obj_fct_is_vectorized=False, options=None):
        super().__init__(objective_function, bounds, obj_fct_is_vectorized, options)
        self.best_score_history = []

    def _update_historic_best(self, positions, scores):
        """Keep track of all historic best scores."""
        best_index, best_score = min(enumerate(scores), key=lambda x: x[1])
        if self.historic_best_score is None or best_score < self.historic_best_score:
            self.historic_best_score = best_score
            self.historic_best_position = positions[best_index]
            self.best_score_history.append(self.HistoryEntry(self.iteration, best_score, positions[best_index]))

    def stop(self):
        """Terminate early if not enough progress is made."""
        def not_enough_progress(required_relative_progress, look_behind=10):
            """Quantify progress in best score over the last iterations.

            Consider the most recent change of the best score that happened at
            least `look_behind` iterations ago. Calculate the difference in
            best score and how many iterations have passed.

            If during this period the best score does not improve a certain amount
            per iteration, return True. The improvement is relative (to the the old
            best score).

            Example: Over the last 10 iterations, the score dropped 3%, i.e., the
            change is -0.3% per iteration. If `required_relative_progress` is
            -0.2%, this is sufficient; while for -0.5% it is not enough progress.

            During the first `look_behind` iterations, always return False.
            """
            if self.iteration < look_behind:
                return False

            iteration_cutoff = self.iteration - look_behind
            last_improvement_before_cutoff = [x for x in self.best_score_history if x.iteration <= iteration_cutoff][-1]
            iterations_delta = self.iteration - last_improvement_before_cutoff.iteration

            score_delta = self.historic_best_score - last_improvement_before_cutoff.score
            relative_score_delta = (score_delta / last_improvement_before_cutoff.score) / iterations_delta

            #print("# {}, #Δ {}, scoreΔ {}, rel.s.Δ {}".format(self.iteration, iterations_delta, score_delta, relative_score_delta))

            return relative_score_delta > required_relative_progress  # remember that both values are negative

        if self.iteration >= self.options['max_iters']:
            return True
        elif self.options.get('required_progress', None) is not None:
            # this is sort of ugly but the options dict might contain None-values (even though that's redundant)
            if self.options.get('required_progress_look_behind', None) is not None:
                return not_enough_progress(self.options['required_progress'],
                                           look_behind=self.options['required_progress_look_behind'])
            else:
                return not_enough_progress(self.options['required_progress'])


class GuidedParticleSwarmOptimizer(EarlyTerminatingParticleSwarmOptimizer):
    """PSO that accepts a hint and spawns particles close to it."""

    def _generate_initial_positions(self):
        search_space_size = self.upper_bound - self.lower_bound
        spread = max(search_space_size / 10)
        # TODO: that magic constant should be configurable on a case-by-case basis
        return clamped_gaussian_distribution(self.options['num_particles'], mean_point=self.options['hint'],
                                             bounds=(self.lower_bound, self.upper_bound),
                                             standard_deviation=spread)


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

        if hint is not None:
            pso_options['hint'] = [float(rational) for rational in hint.get_point(parameters).coordinates]
            pso = GuidedParticleSwarmOptimizer
        else:
            pso = EarlyTerminatingParticleSwarmOptimizer

        self.pso = pso(self._objective, self.bounds, obj_fct_is_vectorized=True, options=pso_options)
        self.pso.initialize()

    def _objective(self, list_of_coords):
        """Perform model checking on the MC instances, convert input/output."""
        rational_points = [_coords_to_rational_point(coords) for coords in list_of_coords]
        parameter_instantiations = self.parameters.instantiate(rational_points)

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
        raise StopIteration
