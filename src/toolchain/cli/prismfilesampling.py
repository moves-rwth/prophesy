#!/usr/bin/env python3

import sys
import os
# import library. Using this instead of appends prevents naming clashes..
thisfilepath =  os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))
#!/usr/bin/env python3

import argparse
from modelcheckers.prism import *
from input.prismfile import *
from sampling import *


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Perform sampling on a prism file')
    
    parser.add_argument('--file',  help='the input file containing the prism file', required=True)
    parser.add_argument('--pctl-file',  help='a file with a pctl property', required=True)
    parser.add_argument('--samples-file', help='resulting file',default="samples.out")
    parser.add_argument('--samplingnr', help='number of samples per dimension', default=4)
    
    solver_group = parser.add_mutually_exclusive_group(required=True)
    solver_group.add_argument('--prism', help='the location of the prism binary')
    solver_group.add_argument('--storm', help='the location of the storm binary')
    cmdargs = parser.parse_args()
    
    prism_file = PrismFile(vars(cmdargs)["file"])
    
    if vars(cmdargs)["prism"] != None:
        tool = PrismModelChecker(vars(cmdargs)["prism"])
    elif vars(cmdargs)["storm"] != None:
        raise NotImplementedError
    else:
        raise RuntimeError("No supported solver available")
    
    print("Perform sampling using " + tool.version())
    
    
    intervals = [(0, 1)] * prism_file.nr_parameters()
    
    samples = perform_uniform_sampling(tool, prism_file, vars(cmdargs)["pctl_file"], intervals, vars(cmdargs)['samplingnr'])
    write_samples_file(prism_file.parameters, samples, vars(cmdargs)["samples_file"])
    
    