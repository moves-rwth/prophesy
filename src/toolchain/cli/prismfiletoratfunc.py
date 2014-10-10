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
    solver_group.add_argument('--param-bin',help='the location of the param binary')
    solver_group.add_argument('--pstorm-bin', help='the location of the pstorm binary')
    solver_group.add_argument('--comics-bin',  help='the location of the comics binary')
    cmdargs = parser.parse_args()
    
    print(vars(cmdargs))
    
    if vars(cmdargs)["param_bin"] != None:
        raise NotImplementedError
    elif vars(cmdargs)["pstorm_bin"] != None:
        tool = ProphesyParametricModelChecker(vars(cmdargs)["pstorm_bin"])
    elif vars(cmdargs)["comics_bin"] != None:
        raise NotImplementedError
    else:
        raise RuntimeError("No supported solver available")
          
    print(tool.name())