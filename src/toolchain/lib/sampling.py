import re
from math import hypot
import math

from data.range import *

class McSampling():
    def __init__(self, tool, prism_file, pctl_filepath):
        self.tool = tool
        self.prism_file = prism_file
        self.pctl_filepath = pctl_filepath
        

    def perform_uniform_sampling(self, intervals, samples_per_dimension):
        assert(samples_per_dimension > 0)
        if samples_per_dimension == 1: raise NotImplementedError
        if self.prism_file.nr_parameters() != len(intervals):
            raise RuntimeError("Number of ranges does not match number of parameters")
        
        ranges = [create_range_from_interval(i, samples_per_dimension) for i in intervals]
        
        return self.tool.uniform_sample_pctl_formula(self.prism_file, self.pctl_filepath, ranges)

    def perform_sampling(self, samplepoints):
        return tool.sample_pctl_formula(prism_file, pctl_filepath, samplepoints)

# Sampling for rational function
class RatFuncSampling():
    def __init__(self, ratfunc, parameters):
        self.parameters = parameters
        self.ratfunc = ratfunc


    def perform_uniform_sampling(self,intervals, samples_per_dimension):
        ranges = [create_range_from_interval(i, samples_per_dimension) for i in intervals]
        return _recursive_substitution(self.ratfunc, self.parameters, ranges, dict())

    def perform_sampling(self, samplepoints):
        samples = dict()
        for pt in samplepoints:
            samples[pt] = self.ratfunc.evaluate(zip(self.parameters, pt))
        return samples


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
    
def write_samples_file(parameters, samples_dict, path):
    with open(path, "w") as f:
        f.write(" ".join(parameters)+"\n")
        for k,v in samples_dict.items():
            f.write("\t".join([("%.4f" % (c)) for c in k ]) + "\t\t" + "%.4f" % (v) + "\n")

def parse_samples_file(path):
    samples = dict()
    with open(path, "r") as f:
        firstLine = True
        lineNumber = 0
        for line in f:
            line = line.strip()
            lineNumber = lineNumber + 1
            if firstLine:
                firstLine = False
                parameters = re.split("\s+", line)
            else:
                lvec = re.split("\s+", line)
                point = tuple([float(c) for c in lvec[:-1]])
                if len(point) != len(parameters):
                    raise RuntimeError("Invalid input on line " + str(lineNumber))
                samples[point] = float(lvec[-1])
    return (samples, parameters)

    
def split_samples(samples, threshold, greaterEqualSafe=True):
    """
    returns (safe, bad)
    """
    below_threshold = dict([(k, v) for k,v in samples.items() if v < threshold])
    above_threshold = dict([(k, v) for k,v in samples.items() if v >= threshold])
    if greaterEqualSafe:
        return (above_threshold, below_threshold)
    else:
        return (below_threshold, above_threshold)
    
def _distance(p1, p2):
    return hypot(p1[0]-p2[0], p1[1]-p2[1])


def filter_sampling(samples, threshold):
    for samplept, sampleval in list(samples.items()):
        if abs(threshold - sampleval) > 0.2:
            del samples[samplept]
    return samples
    
def near_sampling(samples, threshold, rectangles, limit = 0.1, added_dist = 0.05):
    pass
    
    
def refine_sampling(samples, threshold, sampling_interface, greaterEqualSafe = True, use_filter = False):
    bd = 0.1
    samplenr = math.sqrt(len(samples))
    
    if use_filter:
        fsamples = filter_sampling(samples.copy(), threshold)
        (safe_samples, bad_samples) = split_samples(fsamples, threshold, greaterEqualSafe)
    else:
        fsamples = samples
        (safe_samples, bad_samples) = split_samples(samples, threshold, greaterEqualSafe)
    epsilon = (1-2*bd)/(samplenr-1)
    delta = math.sqrt(2*(epsilon*epsilon) + epsilon/2)
    skipCount = 0
    prod = len(safe_samples) * len(bad_samples)
    #print("delta: {0}".format(delta))
    for safe_pt, safe_v in safe_samples.items():
        for bad_pt, bad_v in bad_samples.items():
            #print(totalCount/prod)
            dist = _distance(safe_pt, bad_pt)
            #print("safe_pt: {0}".format(safe_pt))
            #print("bad_pt: {0}".format(bad_pt))
            #print("distance: {0}".format( dist))   
            if dist < delta and dist > 0.06:
                #constructCount = constructCount + 1
                #if constructCount % 10  == 0:
                    #print("constructCount {0}".format(constructCount))
                dist_to_safe = abs(safe_v - threshold)
                dist_to_bad = abs(threshold - bad_v)
                
                safe_weight = (dist_to_safe + 0.2) / (dist_to_safe + dist_to_bad + 0.4)
                bad_weight  = (dist_to_bad  + 0.2) / (dist_to_safe + dist_to_bad + 0.4)
                #print("safe_weight: {0}".format(safe_weight))
                #print("bad_weight: {0}".format(bad_weight))
                assert( abs(safe_weight + bad_weight - 1) < 0.05 )
                
                p = tuple([(safe_weight*i_gs + bad_weight* i_bs)for i_gs, i_bs in zip(safe_pt,bad_pt)])
                skip = False
                i = 0
                for samplept in fsamples.keys():
                    d = _distance(samplept, p)
                    if d < 0.01:
                        skip = True
                        skipCount = skipCount + 1
                        break
                    elif d < 0.05:
                        i = i + 1
                        if i > 2:
                            skip = True
                            skipCount = skipCount + 1
                            break
                        
                        
                #print("p: {0}".format(p))
                #print(samples)
                
                if not skip:
                    samples.update(sampling_interface.perform_sampling([p]))
                
                print("skipCount {0}".format(skipCount))
                #print(samples)
    return samples
