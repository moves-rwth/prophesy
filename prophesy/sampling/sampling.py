from sampling.sampling_uniform import UniformSampleGenerator

import config


def uniform_samples(interface, intervals, samples_per_dim):
    """Generate a uniform grid of samples."""
    samples = {}
    uniform_generator = UniformSampleGenerator(interface, intervals, samples_per_dim)

    for new_samples in uniform_generator:
        samples.update(new_samples)


    return samples



def split_samples(samples, threshold):
    """returns (>=, <)"""
    above_threshold = dict([(k, v) for k, v in samples.items() if v >= threshold])
    below_threshold = dict([(k, v) for k, v in samples.items() if v < threshold])
    return above_threshold, below_threshold

def filter_samples(samples, threshold, distance=config.DISTANCE):
    """Returns samples which are less than (or equal) `distance` away
       from the threshold"""
    return {pt: val for pt, val in samples.items() if abs(threshold - val) <= distance}



