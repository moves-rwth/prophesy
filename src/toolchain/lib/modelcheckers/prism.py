import tempfile
import subprocess

import re

from modelcheckers.pmc import ProbablisticModelChecker
import config
from util import *

def parse_prism_result_file(path):
    samples = {}
    with open(path, 'r') as f:
        firstLine = True
        for line in f:
            lncontent = re.split("\s+", line)
            if firstLine:
                parameters = lncontent[:-2]
                firstLine = False
            else:
                samples[tuple([float(s) for s in lncontent[:-2]])] = float(lncontent[-2])
    print(parameters)
    print(samples)
    return (parameters, samples)
        

class PrismModelChecker(ProbablisticModelChecker):
    def __init__(self, location):
        self.location = location
    
    def name(self):
        return "prism"
    
    def version(self):
        args = [self.location, '-version']
        pipe = subprocess.Popen(args, stdout=subprocess.PIPE)
        #pipe.communicate()
        return pipe.communicate()[0].decode(encoding='UTF-8')
    
    def uniform_sample_pctl_formula(self, prism_file, pctl_filepath, parameters, ranges):
        assert(len(parameters) == len(ranges))
        check_filepath_for_reading(pctl_filepath, "pctl file")
        
        
        range_strings = ["{0}:{1}:{2}".format(r.start, r.step, r.stop) for r in ranges]
        const_values_string = ",".join(["{0}={1}".format(p, r) for (p,r) in zip(parameters, range_strings)])
        
        ensure_dir_exists(config.CLI_INTERMEDIATE_FILES_DIR)
        (resultfd, resultpath) = tempfile.mkstemp(suffix=".txt",dir=config.CLI_INTERMEDIATE_FILES_DIR, text=True)
        
        args = [self.location, prism_file.location, pctl_filepath, 
                "-const",  const_values_string,
                "-exportresults", resultpath]
        run_tool(args)
        (found_parameters, samples) = parse_prism_result_file(resultpath)
        if found_parameters != parameters:
            raise RuntimeError("Prism returns parameters different from the parameters in the prism file")
        return samples
        
        
        
        