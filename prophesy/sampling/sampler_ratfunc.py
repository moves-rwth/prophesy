import logging

from prophesy.sampling.sampler import Sampler
from prophesy.data.samples import InstantiationResultDict, InstantiationResult

logger = logging.getLogger(__name__)

class RatFuncSampling(Sampler):
    """Simple sampler based on pycarl rational function"""

    def __init__(self, ratfunc, parameters):
        """
        :param ratfunc: pycarl.RationalFunction (or lower)
        :param parameters: VariableOrder
        """
        super().__init__()

        self.ratfunc = ratfunc
        self.parameters = parameters

    def perform_sampling(self, samplepoints):
        """
        :param samplepoints: iterable of SamplePoint 
        :return: 
        :rtype: InstantiationResultDict
        """
        logging.debug("Sample rational function")
        samples = InstantiationResultDict(parameters=self.parameters)
        for sample_point in samplepoints:
            # TODO wrap the following in a function.
            #for var in self.ratfunc.gather_variables():
            #    assert var in sample_point.get_parameters()
            res = self.ratfunc.evaluate(sample_point)
            samples[sample_point] = res
        return samples
