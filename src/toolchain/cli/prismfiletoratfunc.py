#!/usr/bin/env python3

"""

"""
import sys
import os
# import library. Using this instead of appends prevents naming clashes..
thisfilepath =  os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))


import argparse
from modelcheckers.pstorm import *

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Transform a prism file to a rational function.')
    
    parser.add_argument('--file',  help='the input file containing the prism file', required=True)
    parser.add_argument('--pctl-file',  help='a file with a pctl property', required=True)
    
    solver_group = parser.add_mutually_exclusive_group(required=True)
    solver_group.add_argument('--param', help='call the param tool')
    solver_group.add_argument('--pstorm', help='the location of the pstorm binary')
    solver_group.add_argument('--comics',  help='the location of the comics binary')
    cmdargs = parser.parse_args()
    
    print(vars(cmdargs))
    
    if vars(cmdargs)["param"] != None:
        raise NotImplementedError
    elif vars(cmdargs)["pstorm"] != None:
        tool = ProphesyParametricModelChecker(vars(cmdargs)["pstorm"])
    elif vars(cmdargs)["comics"] != None:
        raise NotImplementedError
    else:
        raise RuntimeError("No supported solver available")
          
    print("Compute the rational function using " + tool.version())
    tool.get_rational_function(vars(cmdargs)["file"], vars(cmdargs)["pctl_file"])
    
    