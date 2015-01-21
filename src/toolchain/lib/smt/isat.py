import config
import tempfile
from smt.smt import SMTSolver, VariableDomain
from checks import ensure_dir_exists
from util import run_tool

def _constraint_to_isat(constraint):
    return str(constraint.polynomial)[5:].split(",")[0].replace("**", "^") + " " + constraint.relation + " 0"


class IsatSolver(SMTSolver):
    
    def __init__(self, location):
        self.location = location
        self.declstack = [list()]
        self.constraintstack = [list()]
        
    def run(self):
        pass
        
    def stop(self):
        pass
    
    
    def name(self): 
        return "Isat"

    
    def version(self): 
        return "unknown"

    def check(self):
        ensure_dir_exists(config.INTERMEDIATE_FILES_DIR)
        resultfile = tempfile.mkstemp(suffix=".hys",dir=config.CLI_INTERMEDIATE_FILES_DIR, text=True)
        
        with open(resultfile[1], "w") as f:
            f.write("DECL\n")
            for decls in self.declstack:
                for decl in decls:
                    f.write("\t" + decl + ";\n")
            f.write("EXPR\n")
            for constrs in self.constraintstack:
                for constr in constrs:
                    f.write("\t" + constr + ";\n")
        
        print(resultfile[1])
        
        args = [self.location, resultfile[1], "--msw=0.0001", "--prabs=0.00001"]

        print(run_tool(args))
            

    def push(self):
        self.declstack.append([])
        self.constraintstack.append([])

    def pop(self): 
        self.declstack.pop()
        self.constraintstack.pop()

    def add_variable(self, varname, domain): 
        if domain == VariableDomain.Bool:
            s = "boole " + varname
        elif domain == VariableDomain.Real:
            s = "float " + "[0, 1] " + varname
        
        self.declstack[-1].append(s)

    def assert_constraint(self, c): 
        self.constraintstack[-1].append(_constraint_to_isat(c))
        
    def assert_guarded_constraint(self, guard, c):
        self.constraintstack[-1].append(guard + " impl " + _constraint_to_isat(c))

    def set_guard(self, guard, v): 
        if v:
            self.constraintstack[-1].append(guard)
        else:
            self.constraintstack[-1].append("!"+guard)

    def from_file(self, p): raise NotImplementedError

    def to_file(self, p): raise NotImplementedError

    def print_calls(self): 
        pass

        
        