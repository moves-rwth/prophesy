from prophesy.sampling.sampler import Sampler
from prophesy.data.samples import SampleDict

class CarlSampling(Sampler):
    """Sample based on CARL library"""

    def __init__(self, ratfunc, parameters=None):
        """
        @param ratfunc data.RationalFunction
        """
        super().__init__()
        self.ratfunc = ratfunc

    def perform_sampling(self, samplepoints):
        """
        @see Sampler.perform_sampling
        """
        samples = SampleDict()
        for pt in samplepoints:
            value = self.ratfunc.rational_func.evaluate(pt)
            samples[pt] = value
        return samples
