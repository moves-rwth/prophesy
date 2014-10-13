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
    
    match = re.findall('!Result:\s(.*)', inputstring)[0].split("/")
    resultingRatFunNom = match[0]
    if len(match) > 1:
        resultingRatFunDen = match[1]
    
    
    welldefined_constraintsString = re.findall(r'(!Well-formed Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)[0]
    welldefined_constraintsStrings = welldefined_constraintsString.split("\n")[:-1]
    
    
    graphpreserving_constraintsStringList = re.findall(r'(!Graph-preserving Constraints:\s*\n.+?)(?=!|(?:\s*\Z))', inputstring, re.DOTALL)
    if len(graphpreserving_constraintsStringList) > 0:
        graphpreserving_constraintsStrings = graphpreserving_constraintsString[0].split("\n")[:-1]
    else:
        graphpreserving_constraintsStrings = []
    
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
    print(nominator)
    print(denominator)
    return [parameters, wdconstraints, gpconstraints, RationalFunction(nominator, denominator)] 

def write_result_file(parameters, wdconstraints, gpconstraints, rationalfunction, path):
    with open(path, "w") as f:
        f.write("!Parameters: {0}\n".format(", ".join([p.name for p in parameters])))
        f.write("!Result: {0}\n".format(str(rationalfunction)))
        f.write("!Well-formed Constraints:\n{0}\n".format("\n".join([str(c) for c in wdconstraints])))
        f.write("!Graph-preserving Constraints:\n{0}".format("\n".join([str(c) for c in gpconstraints])))
                
