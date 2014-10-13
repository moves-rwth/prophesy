from data.range import *

def perform_uniform_sampling_by_mc(tool, prism_file, pctl_filepath, intervals, samples_per_dimension):
    assert(samples_per_dimension > 0)
    if samples_per_dimension == 1: raise NotImplementedError
    if prism_file.nr_parameters() != len(intervals):
        raise RuntimeError("Number of ranges does not match number of parameters")
    
    ranges = [create_range_from_interval(i, samples_per_dimension) for i in intervals]
    
    return tool.uniform_sample_pctl_formula(prism_file, pctl_filepath, prism_file.parameters, ranges)

def perform_sampling_by_mc(tool, prism_file, pctl_filepath, samplepoints):
    return tool.sample_pctl_formula(prism_file, pctl_filepath, samplepoints)

def _recursive_substitution(rational_function, parameters, ranges, samples, point=None):
    assert(len(parameters) == len(ranges))
    if len(parameters) > 1:
        for v in ranges[0].values():
            if point == None:
                pt = (v,)
            else:
                pt = point + (v,)
            samples = _recursive_substitution(rational_function.substitute(parameters[0], v), parameters[1:], ranges[1:], samples, pt)
    else:   
        for v in ranges[0].values():
            res = rational_function.evaluate([[parameters[0], v]])
            if point == None:
                samples[(v,)] = res
            else:
                samples[point + (v,)] = res        
    return samples
    
def perform_uniform_sampling_by_rf(parameters, rational_function, intervals, samples_per_dimension):
    ranges = [create_range_from_interval(i, samples_per_dimension) for i in intervals]
    return _recursive_substitution(rational_function, parameters, ranges, dict())
    


    
    

def write_samples_file(parameters, samples_dict, path):
    with open(path, "w") as f:
        f.write(" ".join(parameters)+"\n")
        for k,v in samples_dict.items():
            f.write("\t".join([("%.4f" % (c)) for c in k ]) + "\t\t" + "%.4f" % (v) + "\n")
    
    
    