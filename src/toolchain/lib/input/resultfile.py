import re
from sympy import Symbol
from sympy.polys import Poly
from data.constraint import Constraint
from data.rationalfunction import RationalFunction


def read_result_file(input_path):
    inputfile = open(input_path)
    inputstring = inputfile.read()
    inputfile.close()
   
    parameters = re.findall('!Parameters:\s(.*)', inputstring)[0].split(", ")
    
    match = re.search('!Result:\s*((\w|[)(\+\*\^-])*?)(\s?/\s?((\w|[)(\+\*\^-])*?))?\n', inputstring)
    resultingRatFunNom = match.group(1)
    resultingRatFunDen = match.group(4)
    
    welldefined_constraintsString = re.findall(r'(!Well-formed Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)[0]
    welldefined_constraintsStrings = welldefined_constraintsString.split("\n")[:-1]
    
    
    graphpreserving_constraintsString = re.findall(r'(!Graph-preserving Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)[0]
    graphpreserving_constraintsStrings = graphpreserving_constraintsString.split("\n")[:-1]
    
    return [parameters, welldefined_constraintsStrings, graphpreserving_constraintsStrings, resultingRatFunNom, resultingRatFunDen]

def parse_result_file(path):
    [parameter_strings, welldefined_constraint_strings, graph_preserving_constraint_strings, nominator_string, denominator_string] = read_result_file(path)
    parameters = [ Symbol(name.rstrip()) for name in parameter_strings ]
    wdconstraints = [ Constraint.__from_str__(cond, parameters) for cond in welldefined_constraint_strings[1:] ]
    gpconstraints = [ Constraint.__from_str__(cond, parameters) for cond in graph_preserving_constraint_strings[1:] ]
    nominator = Poly(nominator_string, parameters)
    denominator = Poly(1, parameters)
    if denominator_string != None:
        denominator = Poly(denominator_string, parameters)
        
    return [parameters, wdconstraints, gpconstraints, RationalFunction(nominator, denominator)] 

def write_result_file(parameters, wdconstraints, gpconstraints, rationalfunction, path):
    pass
