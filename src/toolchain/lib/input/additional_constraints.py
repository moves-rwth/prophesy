from sympy import Symbol
from data.constraint import Constraint


def constraints_from_file(filepath, parameters):
    inputfile = open(filepath, 'r')
    constraints = []
    safity = None
    line = inputfile.readline()
    if "SAFE" in line:
        safity = True;
    elif "BAD" in line:
        safity = False;
    else:
        pass
        # throw error.
    for line in inputfile:
        constraints.append(Constraint.__from_str__(line, parameters))
    inputfile.close()
    return safity, constraints
