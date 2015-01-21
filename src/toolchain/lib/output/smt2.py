import subprocess
import re
import os
from config import TMP_DIR, Z3_COMMAND, SUPPORT
from sympy.polys.polytools import Poly
from data.constraint import Constraint

def __smt2_filepath_from_name(name):
    path = os.path.join(INTERMEDIATE_FILES, SMT2_SUBDIR)
    if not os.path.exists(path):
        os.makedirs(path)
    return os.path.join(path, name) + '.smt2'


def check_samplepoint_smt2(variables, point, constraints):
    formula = "(set-logic QF_NRA)\n"
    formula += "(set-info :smt-lib-version 2.0)\n"
    # define variables
    for x in variables:
        formula += "(declare-fun " + x.name + " () Real)\n"
    print(point)
    for v, p in zip(variables, point):
        formula += "(assert (=  " + v.name + " " + str(p) + "))\n"
    for c in constraints:
        if c == None:
            pass
        else:
            formula += "(assert " + c.__str__() + ")\n"
    formula += "(check-sat)\n"
    formula += "(exit)\n"
    f = open(os.path.join(TMP_DIR, "sample-check") + ".smt2", 'w')
    f.write(formula)
    f.close()

    args = [Z3_COMMAND, os.path.join(TMP_DIR, "sample-check") + ".smt2"]
    pipe = subprocess.Popen(args, stdout = subprocess.PIPE)
    # pipe.communicate()
    output = pipe.communicate()[0]

    smtres = re.findall("(sat|unsat)", str(output))[0]

    if smtres == "sat":
        return True
    else:
        return False

def generate_smt2(variables, constraints, objective_nominator, objective_denominator, threshold, excluded_areas = [], upper = True):
    """ 
      @param variables Set of all variables occurring in the system.
      @param conditions A list of constraints representing the side conditions.
      @param objective The objective function being a Poly object.
    """
    assert isinstance(variables, list) and isinstance(constraints, list) and isinstance(objective_nominator, Poly)

    if upper:
        relation = "<="
    else:
        relation = ">="

    objective_constraint = Constraint(objective_nominator - threshold * objective_denominator, relation, list(variables))
    variable_names = [ v.name for v in variables ]
    formula = "(set-logic QF_NRA)\n"
    formula += "(set-info :source |\n"
    formula += "Probabilistic verification" + "\n"
    formula += SUPPORT + "\n"
    formula += "|)\n"
    formula += "(set-info :smt-lib-version 2.0)\n"
    formula += "(set-info :category \"industrial\")\n"
    # define variables
    for x in variable_names:
        formula += "(declare-fun " + x + " () Real)\n"
    # define assertion

    # conditions
    for c in constraints:
        if c == None:
            pass
        else:
            formula += "(assert " + c.__str__() + ")\n"
    for a in excluded_areas:
        formula += "(assert (not (and "
        for c in a:
            if c == None:
                pass
            else:
                formula += c.__str__()
        formula += ") ) )\n"
    formula += "(assert\n"

    formula += " " + objective_constraint.__str__()
    formula += "\n  )\n"
    formula += "(check-sat)\n"
    formula += "(get-model)\n"
    formula += "(exit)\n"
    return formula

def smt2_to_file(name, variables, constraints, objective_nominator, objective_denominator, threshold, excluded_areas, upper = True):
    f = open(__smt2_filepath_from_name(name), 'w')
    f.write(generate_smt2(variables, constraints, objective_nominator, objective_denominator, threshold, excluded_areas, upper))
    f.close()

def call_smt_solver(solver, name):
    if(solver == "z3"):
        args = [Z3_COMMAND, __smt2_filepath_from_name(name)]
        pipe = subprocess.Popen(args, stdout = subprocess.PIPE)
        # pipe.communicate()
        output = pipe.communicate()[0]
        smtres = re.findall("(sat|unsat)", str(output))[0]
        model = None
        if smtres == "sat":
            model = {}
            modelValues = re.compile(r"\(define-fun\s(\w+)\s\(\)\sReal.*?\(/\s(\d+(\.\d+)?)\s(\d+(\.\d+)?)\)\)", re.MULTILINE)
            for match in modelValues.finditer(str(output)):
                print(match.group(1))
                print(match.group(2))
                print(match.group(4))
                model[match.group(1)] = float(match.group(2)) / float(match.group(4))
            # print(re.findall("\(define-fun\s\w+\s\(\)\sReal\s\(/\d+(\.\d+)?\s\d+(\.\d+)?\s\)\)", str(output)))
            print("SATISFIED")
        else:
            print("UNSATISFIED")
        return (smtres, model)
    else:
        print("Not yet supported")
