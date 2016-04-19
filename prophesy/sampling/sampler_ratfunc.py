from sampling.sampler import Sampler
from data.samples import SampleDict

class RatFuncSampling(Sampler):
    """Simple sampler based on pycarl rational function"""

    def __init__(self, ratfunc, parameters=None):
        """
        @param ratfunc pycarl.RationalFunction (or lower)
        @param parameters set of pycarl.Variable (optional)
        """
        super().__init__()

        self.ratfunc = ratfunc
        self.variables = self.ratfunc.gather_variables()

    def perform_sampling(self, samplepoints):
        """
        @param samplepoints iterable of SamplePoint (pref.SamplePoints)
        @return SampleDict
        """
        samples = SampleDict()
        for pt in samplepoints:
            samples[pt] = self.ratfunc.eval(pt)
        return samples
