class SampleGenerator(object):
    """Class to refine a given set of samples
    """
    def __init__(self, sampler, intervals):
        """
        @param Sampler used to generate new samples
        @param intervals iterable of Interval in between which to sample
        """
        self.sampler = sampler
        self.intervals = intervals

    def refine_samples(self):
        """Based on current set of known samples, generate a refinement which
        samples closer to the estimated threshold boundaries.
        """
        raise NotImplemented()
