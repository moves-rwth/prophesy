from prophesy.sampling.sampling_pso import ParticleSwarmSampleGenerator
from prophesy.data.samples import InstantiationResult
import logging
logger = logging.getLogger(__name__)

class ModelOptimizer:
    """Finds arg-{min,max} of PCTL property values."""

    def __init__(self, modelchecker, parameters, pctl_property, direction, region=None):
        self._direction = direction
        self.modelchecker = modelchecker
        modelchecker.set_pctl_formula(pctl_property)
        self._pso_sample_gen = ParticleSwarmSampleGenerator(modelchecker, parameters, self.score, region=region)
        self._parameters = parameters
        self._threshold = None
        self._iterations = 0

    def set_termination_threshold(self, threshold):
        self._threshold = threshold

    def score(self, _, value):
        """Invert value depending on {min,max}, since PSO minimizes score."""
        # _ is parameter_instantiation, which we don't care about here
        return value if self._direction == 'min' else -value

    @property
    def iterations(self):
        return self._iterations

    def search(self):
        """Run PSO and return best result."""
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
                        self.modelchecker.sample_single_point
                        break
                if self._direction == "min":
                    if value < self._threshold:
                        break

        print(self.score(None, self._pso_sample_gen.pso.historic_best_score))
        return InstantiationResult.from_point(self._pso_sample_gen.pso.historic_best_position, self.score(None, self._pso_sample_gen.pso.historic_best_score), self._parameters)