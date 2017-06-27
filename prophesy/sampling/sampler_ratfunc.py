import logging

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
            # TODO wrap the following in a function.
            #for var in self.ratfunc.gather_variables():
            #    assert var in sample_point.get_parameters()
            logging.debug("....")
            res = self.ratfunc.evaluate(dict([(k.variable, v) for k,v in sample_point.items()]))
            logging.debug("={}".format(res))
            samples.add_result(InstantiationResult(sample_point, res))
        return samples
