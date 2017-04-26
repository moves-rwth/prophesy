from prophesy.sampling.sample_generator import SampleGenerator

class UniformSampleGenerator(SampleGenerator):
    """Generates a uniform grid of samples"""

    def __init__(self, sampler, variables_and_intervals, samples, samples_per_dimension):
        super().__init__(sampler, variables_and_intervals[0], samples)
        self.variables_and_intervals = variables_and_intervals
        self.samples_per_dimension = samples_per_dimension

    def __iter__(self):
        # There is a special uniform function for samplers (optimization case for PRISM)
        yield self.sampler.perform_uniform_sampling(self.variables_and_intervals, self.samples_per_dimension)
