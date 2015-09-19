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

    constraints_string = re.findall('Constraints:\n((.*?\n)*?)\n', inputstring)[0][0]
    constraints_strings = constraints_string.split("\n")[:-1]
    print(constraints_strings)
    match = re.search('Model Checking result:\s*((\w|[)(\+\*\^-])*?)(\s?/\s?((\w|[)(\+\*\^-])*?))?\n', inputstring)
    resulting_ratfun_nom = match.group(1)
    resulting_ratfun_den = match.group(4)
    print(resulting_ratfun_nom)
    print(resulting_ratfun_den)
    return [parameters, constraints_strings, resulting_ratfun_nom, resulting_ratfun_den]


def get_polynomials_from_comics_file(path):
    [parameter_strings, constraint_strings, nominator_string, denominator_string] = read_comics_file(path)

    parameters = [Symbol(name) for name in parameter_strings]
    constraints = [Constraint.__from_str__(cond, parameters) for cond in constraint_strings]

    nominator = Poly(nominator_string, parameters)
    denominator = Poly(1, parameters)
    if denominator_string != None:
        denominator = Poly(denominator_string, parameters)

    return [parameters, constraints, nominator, denominator]
