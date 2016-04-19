from prophesy.sampling.sampler import Sampler
from prophesy.data.samples import SampleDict

class RatFuncSampling(Sampler):
    """Simple sampler based on pycarl rational function"""

    def __init__(self, ratfunc, variables=None):
        """
        @param ratfunc pycarl.RationalFunction (or lower)
        @param variables VariableOrder (Optional)
        """
        super().__init__()

        self.ratfunc = ratfunc
        self.variables = variables

    def perform_sampling(self, samplepoints):
        """
        @param samplepoints iterable of SamplePoint (preferably SamplePoints)
        @return SampleDict
        """
        samples = SampleDict(self.variables)
        for pt in samplepoints:
            samples[pt] = self.ratfunc.eval(pt)
        return samples
