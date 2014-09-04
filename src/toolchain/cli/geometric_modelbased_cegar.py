#!/bin/python3 
import subprocess
import argparse
import sys
import numpy as np
import iterable_param
import shlex
import re
import output

McInputFile = 'storm_inputfile.tmp'

parser = argparse.ArgumentParser(description='Use a model to synthesise its fulfilling parameter values.')
parser.add_argument('--file',  help='the input file containing parameters', required=True)
parser.add_argument('--storm', help='path to storm')
parser.add_argument('--prism', help='path to prism')
parser.add_argument('--property', help='property to be checked', required=True)
parser.add_argument('--samples', type=int, help='sample points in each dimension (default: 4)', default=4)
cmdargs = parser.parse_args()

useStorm = True
if vars(cmdargs)['storm'] == None:
    if vars(cmdargs)['prism'] == None:
        print('Either storm or prism are required as a backend')
        sys.exit(1)
    else:
        useStorm = False
    

# Find variables
# Create temporary file renaming param to const.
inputfile = open(vars(cmdargs)['file'])
outputfile = open(McInputFile, 'w')
parameters = []
for line in inputfile:
    if 'param' in line and line[:2] != "//":
        parameters.append(line.split()[2][:-1])
        outputfile.write(line.replace('param', 'const'))
    else:
        outputfile.write(line)
print(parameters)

inputfile.close()
outputfile.close()

result = {}
for x in iterable_param.IterableParam(parameters,vars(cmdargs)['samples']):
    constantString = ','.join("{!s}={:.9f}".format(key,val) for (key,val) in x.items())
    
    # Call model checker
    if useStorm:
        subprocess.call([vars(cmdargs)['storm'], "--symbolic " + McInputFile])
    else:
        call = vars(cmdargs)['prism'] + " " + McInputFile + " " + vars(cmdargs)['property'] + " -const " + constantString
        args = shlex.split(call)
        print(call)
        pipe = subprocess.Popen(args, stdout=subprocess.PIPE)
        #pipe.communicate()
        output =  pipe.communicate()[0]
        mcres =  re.findall("Result: (true|false)", str(output))[0]
        result[x.values()] = mcres == 'true'
        
output.print_result(result)
output.plot_result(parameters, result)


        


