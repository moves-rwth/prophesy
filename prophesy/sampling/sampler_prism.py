from sampling.sampling import Sampler
from collections import OrderedDict
import data.range

class McSampling(Sampler):
    """Perform sampling based on the PRISM tool"""
    def __init__(self, tool, prism_file, pctl_file):
        super().__init__()

        self.tool = tool
        self.prism_file = prism_file
        self.pctl_file = pctl_file

    def perform_uniform_sampling(self, intervals, samples_per_dimension):
        assert samples_per_dimension > 1
        ranges = [data.range.create_range_from_interval(interval, samples_per_dimension) for interval in intervals]
        samples = self.tool.uniform_sample_pctl_formula(self.prism_file, self.pctl_file, ranges)
        return OrderedDict(samples.items())

    def perform_sampling(self, sample_points):
        samples = self.tool.sample_pctl_formula(self.prism_file, self.pctl_file, sample_points)
        return OrderedDict(samples.items())
