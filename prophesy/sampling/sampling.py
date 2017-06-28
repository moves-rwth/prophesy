"""
Helper module for simplified sampling access.
"""
from prophesy.sampling.sampling_uniform import UniformSampleGenerator
from prophesy.data.samples import InstantiationResultDict
from prophesy.sampling.sampling_linear import LinearRefinement


def uniform_samples(sampler, parameters, samples_per_dim):
    """
    Generate a uniform grid of samples.
    
    :param sampler: The sampler to use 
    :param parameters: The parameters in our problem
    :param samples_per_dim: The number of samples per dimension
    :return:
    """
    # TODO simplify uniform sampling in a subregion.
    # TODO make sure that if uniform sampling is implemented for the sampler, that we use that one.
    samples = InstantiationResultDict(parameters)
    uniform_generator = UniformSampleGenerator(sampler, parameters, samples, samples_per_dim)

    for new_samples in uniform_generator:
        samples.update(new_samples)

    return samples


def refine_samples(sampler, parameters, samples, iterations, threshold):
    """
    Refine samples over several iterations.
    
    :param sampler: The sampler to use 
    :param parameters: The parameters of the problem
    :param samples: The already known samples
    :param iterations: The number of iterations the refinement generator should be called.
    :param threshold: The threshold value we are most interested in
    :return: 
    """
    refinement_generator = LinearRefinement(sampler, parameters, samples, threshold)

    # Using range to limit the number of iterations
    for (i, new_samples) in zip(range(0, iterations), refinement_generator):
        # uncomment to see intermediate plot before each iteration
        # open_file(plot_samples(samples, result.parameters, True, threshold))

        samples.update(new_samples)

    return samples
