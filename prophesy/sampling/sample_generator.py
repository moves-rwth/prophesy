from prophesy import config
from prophesy.data.samples import SampleDict

class SampleGenerator(object):
    """Class to generate samples given a sampler. SampleGenerator uses the
    iteration interface to do so.
    """

    def __init__(self, sampler, variables, samples):
        """
        @param sampler Sampler used to generate new samples
        @param variables VariableOrder
        @param samples SampleDict pre-existing samples, which is copied.
            None is allowed
        """
        self.sampler = sampler
        self.variables = variables
        self.samples = samples.copy() if samples else SampleDict(self.variables)
        self.distance = config.DISTANCE
