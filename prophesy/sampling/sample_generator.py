from prophesy.config import configuration
from prophesy.data.samples import InstantiationResultDict


class SampleGenerator:
    """Class to generate samples given a sampler. SampleGenerator uses the
    iteration interface to do so.
    """

    def __init__(self, sampler, parameters, samples = None):
        """
        @param sampler Sampler used to generate new samples
        @param parameters VariableOrder
        @param samples SampleDict pre-existing samples, which is copied.
            None is allowed
        """
        self.sampler = sampler
        self.parameters = parameters
        self.samples = samples.copy() if samples else InstantiationResultDict(parameters=parameters)
        self.distance = configuration.get_sampling_min_distance()
