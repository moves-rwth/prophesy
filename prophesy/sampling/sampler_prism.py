from prophesy.sampling.sampler import Sampler
from prophesy.data import range

class McSampling(Sampler):
    """Perform sampling based on the PRISM input file"""
    def __init__(self, tool):
        super().__init__()

        self.tool = tool

    def perform_uniform_sampling(self, intervals, samples_per_dimension):
        assert samples_per_dimension > 1
        ranges = [range.create_range_from_interval(interval, samples_per_dimension) for interval in intervals]
        samples = self.tool.uniform_sample(ranges)
        return samples

    def perform_sampling(self, sample_points):
        samples = self.tool.sample(self.prism_file, self.pctl_file, sample_points)
        return samples
