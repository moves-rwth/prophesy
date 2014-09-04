import re
from sympy import Symbol
from sympy.polys import Poly
from data.constraint import Constraint


def read_comics_file(input_path):
    inputfile = open(input_path)
    inputstring = inputfile.read()
    inputfile.close()

    parameters = re.findall('Parameters:\n(.*)', inputstring)[0].split(", ")
    print(parameters)
    
    constraintsString = re.findall('Constraints:\n((.*?\n)*?)\n', inputstring)[0][0]
    constraintsStrings = constraintsString.split("\n")[:-1]
    print(constraintsStrings)
    match = re.search('Model Checking result:\s*((\w|[)(\+\*\^-])*?)(\s?/\s?((\w|[)(\+\*\^-])*?))?\n', inputstring)
    resultingRatFunNom = match.group(1)
    resultingRatFunDen = match.group(4)
    print(resultingRatFunNom)
    print(resultingRatFunDen)
    return [parameters, constraintsStrings, resultingRatFunNom, resultingRatFunDen]

def get_polynomials_from_comics_file(path):
    [parameter_strings, constraint_strings, nominator_string, denominator_string] = read_comics_file(path)
    parameters = [ Symbol(name) for name in parameter_strings ]
    constraints = [ Constraint.__from_str__(cond, parameters) for cond in constraint_strings ]
    nominator = Poly(nominator_string, parameters)
    denominator = Poly(1, parameters)
    if denominator_string != None:
        denominator = Poly(denominator_string, parameters)
    return [parameters, constraints, nominator, denominator]  
