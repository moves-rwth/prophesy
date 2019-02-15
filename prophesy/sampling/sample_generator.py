import prophesy.config
from prophesy.data.samples import InstantiationResultDict


class SampleGenerator:
    """Class to generate samples given a sampler. SampleGenerator uses the
    iteration interface to do so.
    """

    def __init__(self, sampler, parameters, region, samples = None):
        """
        @param sampler Sampler used to generate new samples
        @param parameters VariableOrder
        @param samples SampleDict pre-existing samples, which is copied.
            None is allowed
        """
        self.sampler = sampler
        self.parameters = parameters
        self.region = region
        self.samples = samples.copy() if samples else InstantiationResultDict(parameters=parameters)
        assert prophesy.config is not None
        self.distance = prophesy.config.configuration.get_sampling_min_distance()
