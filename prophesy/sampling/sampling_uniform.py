from prophesy.sampling.sample_generator import SampleGenerator

class UniformSampleGenerator(SampleGenerator):
    """Generates a uniform grid of samples"""

    def __init__(self, sampler, intervals, samples_per_dimension):
        super().__init__(sampler, intervals)
        self.samples_per_dimension = samples_per_dimension

    def __iter__(self):
        # There is a special uniform function for samplers (optimization case for PRISM)
        yield self.sampler.perform_uniform_sampling(self.intervals, self.samples_per_dimension)
