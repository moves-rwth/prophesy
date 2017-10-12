from prophesy.sampling.sampling_pso import ParticleSwarmSampleGenerator

class ModelOptimizer:
    """Finds arg-{min,max} of PCTL property values."""

    def __init__(self, modelchecker, parameters, pctl_property, direction):
        self.direction = direction
        modelchecker.set_pctl_formula(pctl_property)
        self._pso_sample_gen = ParticleSwarmSampleGenerator(modelchecker, parameters, self.score)

    def score(self, _, value):
        """Invert value depending on {min,max}, since PSO minimizes score."""
        # _ is parameter_instantiation, which we don't care about here
        return value if self.direction == 'min' else -value

    def search(self):
        """Run PSO and return best result."""
        _ = [None for _ in self._pso_sample_gen]  # exhaust sampling iterator, discarding intermediate results
        return self._pso_sample_gen.pso.historic_best_position, self._pso_sample_gen.pso.historic_best_score