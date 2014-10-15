import subprocess

from smt.smt import SMTSolver
from smt.smt import *
from config import *

import re

def _smtfile_header():
    formula = "(set-logic QF_NRA)\n"
    formula += "(set-info :source |\n"
    formula += "Probabilistic verification" + "\n"
    formula += TOOLNAME + "\n"
    formula += "|)\n"
    formula += "(set-info :smt-lib-version 2.0)\n"
    formula += "(set-info :category \"industrial\")\n"
    return formula

class SmtlibSolver(SMTSolver):
    def __init__(self, location):
        self.location = location
        self.formula = _smtfile_header()
        self.process = None
        self.string = self.formula
    
    def run(self):
        if self.process == None:
            args = [self.location, "-smt2", "-in"]
            self.process = subprocess.Popen(args, stdout=subprocess.PIPE, stdin=subprocess.PIPE, universal_newlines=True)
        else: 
            raise RuntimeError("The solver can only be started once")
        
    def stop(self):
        if self.process != None:
            self.string += "(exit)\n"
            self.process.stdin.write("(exit)\n")
            print(self.process.communicate()[0])
            self.process = None
    
    def name(self): 
       return "smt-lib"

    def version(self): 
        args = [self.location, "--version"]
        p = subprocess.Popen(args, stdout=subprocess.PIPE, stdin=subprocess.PIPE, universal_newlines=True)
        return p.communicate()[0].rstrip()

    def check(self): 
        self.string += "(check-sat)\n"
        self.process.stdin.write("(check-sat)\n")
        self.process.stdin.flush()
        for line in iter(self.process.stdout.readline, ""):
            if self.process.poll() != None:
                break
            output = line.rstrip()
            if output == "unsat":
                print("returns unsat")
                return Answer.unsat
            elif output == "sat":
                print("returns sat")
                return Answer.sat
            else: 
                raise NotImplementedError
        #for line in iter(self.process.stdout.readline, ""):
            #if not line and self.process.poll() != None:
                #break
            #output = line.decode(encoding='UTF-8').rstrip()
            #if output != "":
                #print( "\t * "+ output)

    def push(self): 
        s = "(push)\n"
        self.string += s
        self.process.stdin.write(s)

    def pop(self): 
        s = "(pop)\n"
        self.string += s
        self.process.stdin.write(s)

    def add_variable(self, symbol, domain=VariableDomain.Real): 
        s = "(declare-fun " + symbol + " () "+ domain.name +")\n"
        self.string += s
        self.process.stdin.write(s)

    def assert_constraint(self, constraint): 
        s = "(assert " +  constraint.to_smt2_string() + " )\n"
        self.string += s
        self.process.stdin.write(s)
    
    def assert_guarded_constraint(self, guard, constraint):
        s = "(assert (=> " + guard + " " + constraint.to_smt2_string() + " ))\n"
        self.string += s
        self.process.stdin.write(s)
        
    def set_guard(self, guard, value):
        if value:
            s = "(assert " + guard + " )\n"
        else:
            s = "(assert (not " + guard + " ))\n"
        self.string += s
        self.process.stdin.write(s)
        
    def get_model(self):
        s = "(get-model)\n"
        self.string += s
        self.process.stdin.write(s)
        self.process.stdin.flush()
        output = ""
        for line in iter(self.process.stdout.readline, ""):
            if self.process.poll() != None:
                break
            output += line.rstrip()
            if output.count('(') == output.count(')'):
                break
        model = {}
        modelValues = re.compile(r"\(define-fun\s(\w+)\s\(\)\sReal.*?\(/\s(\d+(\.\d+)?)\s(\d+(\.\d+)?)\)\)",re.MULTILINE)
        for match in modelValues.finditer(str(output)):
            print(match.group(1))
            print(match.group(2))
            print(match.group(4))
            model[match.group(1)] = float(match.group(2))/float(match.group(4))
        return model
        

    def from_file(self, path): raise NotImplementedError

    def to_file(self, path): raise NotImplementedError

    def print_calls(self):
        print(self.string)

    
        