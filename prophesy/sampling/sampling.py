"""
Helper module for ratfilesampling.py
TODO: Should be removed at some point, or moved away
"""
from prophesy.sampling.sampling_uniform import UniformSampleGenerator
from prophesy.sampling.sampling_delaunay import DelaunayRefinement
from prophesy.data.samples import SampleDict

def uniform_samples(interface, parameters, samples_per_dim):
    """Generate a uniform grid of samples."""
    samples = SampleDict()
    uniform_generator = UniformSampleGenerator(interface,
        parameters.get_variable_order(), samples,
        parameters.get_variable_bounds(), samples_per_dim)

    for new_samples in uniform_generator:
        samples.update(new_samples)

    return samples


def refine_samples(interface, parameters, samples, iterations, threshold):
    """Refine samples over several iterations."""
    # refinement_generator = LinearRefinement(interface, samples, threshold)
    refinement_generator = DelaunayRefinement(interface, parameters.get_variable_order(), samples, threshold)

    # Using range to limit the number of iterations
    for (new_samples, i) in zip(refinement_generator, range(0, iterations)):

        # uncomment to see intermediate plot before each iteration
        #open_file(plot_samples(samples, result.parameters, True, threshold))

        print("Refining sampling ({}/{}): {} new samples".format(i + 1, iterations, len(new_samples)))
        samples.update(new_samples)

    return samples
