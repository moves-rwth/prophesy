from sampling.sampling_uniform import UniformSampleGenerator
from sampling.sampling_delaunay import DelaunayRefinement
from sampling.sampling_linear import LinearRefinement

import config


def uniform_samples(interface, intervals, samples_per_dim):
    """Generate a uniform grid of samples."""
    samples = {}
    uniform_generator = UniformSampleGenerator(interface, intervals, samples_per_dim)

    for new_samples in uniform_generator:
        samples.update(new_samples)


    return samples


def refine_samples(interface, intervals, samples, iterations, threshold):
    """Refine samples over several iterations."""
    # refinement_generator = LinearRefinement(interface, samples, threshold)
    refinement_generator = DelaunayRefinement(interface, intervals, samples, threshold)

    # Using range to limit the number of iterations
    for (new_samples, i) in zip(refinement_generator, range(0, iterations)):

        # uncomment to see intermediate plot before each iteration
        #open_file(plot_samples(samples, result.parameters, True, threshold))

        print("Refining sampling ({}/{}): {} new samples".format(i + 1, iterations, len(new_samples)))
        samples.update(new_samples)

    return samples
