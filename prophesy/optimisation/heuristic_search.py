from prophesy.sampling.sampling_pso import ParticleSwarmSampleGenerator
from prophesy.data.samples import InstantiationResult
import prophesy.adapter.pycarl as pc
import logging
logger = logging.getLogger(__name__)

class ModelOptimizer:
    """Finds arg-{min,max} of PCTL property values."""

    def __init__(self, modelchecker, parameters, pctl_property, direction, region=None):
        self._direction = direction
        self._modelchecker = modelchecker
        modelchecker.set_pctl_formula(pctl_property)

        self._pso_sample_gen = None
        self._parameters = parameters
        self._nr_particles = self._compute_nr_particles()
        self._threshold = None
        self._iterations = 0
        self._region = region

    def set_termination_threshold(self, threshold):
        self._threshold = threshold

    def score(self, _, value):
        """Invert value depending on {min,max}, since PSO minimizes score."""
        # _ is parameter_instantiation, which we don't care about here
        return value if self._direction == 'min' else -value

    @property
    def iterations(self):
        return self._iterations

    def _compute_nr_particles(self):
        return 100 if len(self._parameters) < 10 else 800 if len(self._parameters) > 40 else 400

    def _initialise(self):
        """
        Initialise the PSO backend
        """
        pso_options = dict()
        pso_options['num_particles'] = self._nr_particles
        pso_options['max_iters'] = 100000

        if self._threshold is None:
            pso_options['required_progress'] = pc.Rational('-0.01')
            pso_options['required_progress_look_behind'] = 5


        self._pso_sample_gen = ParticleSwarmSampleGenerator(self._modelchecker, self._parameters, self.score, region=self._region, pso_options=pso_options)


    def search(self):
        """Run PSO and return best result."""
        if not self._pso_sample_gen:
            self._initialise()
        for _ in self._pso_sample_gen:
            self._iterations += 1
            if self._threshold is not None:
                assert self._direction in ["max", "min"]
                value = self.score(None, self._pso_sample_gen.pso.historic_best_score)
                InstantiationResult.from_point(self._pso_sample_gen.pso.historic_best_position,
                                               self.score(None, self._pso_sample_gen.pso.historic_best_score),
                                               self._parameters)
                logger.debug("Comparing {} with {}".format(value, self._threshold))
                if self._direction == "max":
                    if value > self._threshold:
                        break
                if self._direction == "min":
                    if value < self._threshold:
                        break
            else:
                logger.debug("PSO has not converged, start a new round of {} samples".format(self._nr_particles))

        return InstantiationResult.from_point(self._pso_sample_gen.pso.historic_best_position, self.score(None, self._pso_sample_gen.pso.historic_best_score), self._parameters)