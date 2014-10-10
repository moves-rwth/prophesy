#!/usr/bin/env python3

"""

"""


import argparse

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Transform a prism file to a rational function.')
    
    parser.add_argument('--file',  help='the input file containing the prism file', required=True)
    parser.add_argument('--pctl-file',  help='a file with a pctl property', required=True)
    
    solver_group = parser.add_mutually_exclusive_group(required=True)
    solver_group.add_argument('--param-bin',help='the location of the param binary')
    solver_group.add_argument('--pstorm-bin', help='the location of the pstorm binary')
    solver_group.add_argument('--comics-bin',  help='the location of the comics binary')
    cmdargs = parser.parse_args()

    if "param-bin" in vars(cmdargs):
        raise NotImplementedError
    elif "pstorm-bin" in vars(cmdargs):
        raise NotImplementedError
    elif "comics-bin" in vars(cmdargs):
        raise NotImplementedError
    else:
        raise RuntimeError("No supported solver available")
            