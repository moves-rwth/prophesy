from prophesy.sampling.sampler import Sampler
from prophesy.data.samples import InstantiationResultDict, InstantiationResult

class RatFuncSampling(Sampler):
    """Simple sampler based on pycarl rational function"""

    def __init__(self, ratfunc, variables):
        """
        @param ratfunc pycarl.RationalFunction (or lower)
        @param variables VariableOrder
        """
        super().__init__()

        self.ratfunc = ratfunc
        self.variables = variables

    def perform_sampling(self, samplepoints):
        """
        @param samplepoints iterable of SamplePoint (preferably SamplePoints)
        @return SampleDict
        """
        samples = InstantiationResultDict(self.variables)
        for sample_point in samplepoints:
            samples.add_result(InstantiationResult(sample_point, self.ratfunc.evaluate(sample_point)))
        return samples
