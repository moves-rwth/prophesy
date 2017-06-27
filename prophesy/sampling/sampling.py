"""
Helper module for simplified sampling access.
"""
from prophesy.sampling.sampling_uniform import UniformSampleGenerator
from prophesy.data.samples import InstantiationResultDict
from prophesy.sampling.sampling_linear import LinearRefinement


def uniform_samples(interface, parameters, samples_per_dim):
    """Generate a uniform grid of samples."""
    samples = InstantiationResultDict(parameters)
    uniform_generator = UniformSampleGenerator(interface, parameters, samples, samples_per_dim)

    for new_samples in uniform_generator:
        samples.update(new_samples)

    return samples


def refine_samples(interface, parameters, samples, iterations, threshold):
    """Refine samples over several iterations."""
    refinement_generator = LinearRefinement(interface, parameters, samples, threshold)

    # Using range to limit the number of iterations
    for (i, new_samples) in zip(range(0, iterations), refinement_generator):

        # uncomment to see intermediate plot before each iteration
        #open_file(plot_samples(samples, result.parameters, True, threshold))

        samples.update(new_samples)

    return samples
