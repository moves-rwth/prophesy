import subprocess
import functools
import config
from config import TOOLNAME
from smt.smt import SMTSolver, Answer, VariableDomain

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
    def __init__(self, location = config.Z3_COMMAND, memout = 2000, timeout = 100):
        self.location = location
        self.formula = _smtfile_header()
        self.process = None
        self.string = self.formula
        self.memout = memout * 1000 * 1000
        self.timeout = timeout * 1000
        self.status = ""

    def run(self):
        if self.process == None:
            args = [self.location, "-smt2", "-in", "-t:" + str(self.timeout), "-memory:" + str(self.memout)]
            self.process = subprocess.Popen(args, stdout = subprocess.PIPE, stdin = subprocess.PIPE, stderr = subprocess.PIPE, universal_newlines = True)
            self.process.stdin.write(self.status)
            self.process.stdin.flush()

        else:
            raise RuntimeError("The solver can only be started once")

    def stop(self):
        if self.process != None:
            self.string += "(exit)\n"
            self.process.stdin.write("(exit)\n")
            self.process = None

    def name(self):
        return "smt-lib"

    def version(self):
        args = [self.location, "--version"]
        p = subprocess.Popen(args, stdout = subprocess.PIPE, stdin = subprocess.PIPE, stderr = subprocess.PIPE, universal_newlines = True)
        return p.communicate()[0].rstrip()

    def check(self):
        assert self.process != None
        s = "(check-sat)\n"
        self.string += s
        self.process.stdin.write(s)
        self.process.stdin.flush()

        errstreamout = ""
        for line in iter(self.process.stdout.readline, ""):
            if not line and self.process.poll() != None:
                break
            output = line.rstrip()
            # errstreamout += self.process.stderr.read()
            print("**\t " + output)
            if output == "unsat":
                print("returns unsat")
                return Answer.unsat
            elif output == "sat":
                print("returns sat")
                return Answer.sat
            elif errstreamout == "(error \"out of memory\")":

                print("MemOut")
                self.stop()
                self.run()
                return Answer.memout
            elif output == "Killed":
                self.stop()
                self.run()
                return Answer.killed
            else:
                raise NotImplementedError

        self.stop()
        self.run()
        # print("err")
        # print(self.process.stderr)
        # print("out")
        # print(self.process.stdout.read().rstrip())
        return Answer.killed
        # for line in iter(self.process.stdout.readline, ""):
            # if not line and self.process.poll() != None:
                # break
            # output = line.decode(encoding='UTF-8').rstrip()
            # if output != "":
                # print( "\t * "+ output)

    def push(self):
        s = "(push)\n"
        self.string += s
        self.process.stdin.write(s)
        self.status += s

    def pop(self):
        s = "(pop)\n"
        self.string += s
        self.process.stdin.write(s)
        self.status += s

    def add_variable(self, symbol, domain = VariableDomain.Real):
        s = "(declare-fun " + symbol + " () " + domain.name + ")\n"
        self.string += s
        self.process.stdin.write(s)
        self.status += s

    def assert_constraint(self, constraint):
        s = "(assert " + constraint.to_smt2_string() + " )\n"
        self.string += s
        self.process.stdin.write(s)
        self.status += s

    def assert_guarded_constraint(self, guard, constraint):
        s = "(assert (=> " + guard + " " + constraint.to_smt2_string() + " ))\n"
        self.string += s
        self.process.stdin.write(s)
        self.status += s

    def set_guard(self, guard, value):
        if value:
            s = "(assert " + guard + " )\n"
        else:
            s = "(assert (not " + guard + " ))\n"
        self.string += s
        self.process.stdin.write(s)
        self.status += s

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
        print("output::" , output)
        model = {}
        (cmd, model_cmds) = parse_smt_command(output)
        if cmd == "error":
            print("Error occured in SMT evaluation, input:")
            print(self.string)
            raise RuntimeError("SMT Error")
        for cmd in model_cmds:
            (_, args) = parse_smt_command(cmd)
            if args[2] == "Real":
                model[args[0]] = parse_smt_expr(args[3])
        return model

    def from_file(self, path): raise NotImplementedError

    def to_file(self, path): raise NotImplementedError

    def print_calls(self):
        print(self.string)

def parse_smt_expr(expr):
    """Calculates given SMT expression "(OP ARG ARG)" as ARG OP ARG.
    Expression may be of arbitrary arity"""
    (cmd, args) = parse_smt_command(expr)
    args = map(parse_smt_expr, args)
    if cmd == "+":
        return functools.reduce(lambda x, y: x+y, args, 0)
    elif cmd == "-":
        return functools.reduce(lambda x, y: x-y, args, 0)
    elif cmd == "*":
        return functools.reduce(lambda x, y: x*y, args, 1)
    elif cmd == "/":
        return functools.reduce(lambda x, y: x/y, args)
    else:
        return float(cmd)

def parse_smt_command(command):
    """Breaks the given SMT command "(CMD ARG ARG ARG)" into tuple (CMD, [ARG]),
    where ARG again can be a (non-parsed) command"""
    command = command.strip()
    if command[0] != "(":
        return (command, [])
    command = command[1:-1].split(maxsplit=1)
    if len(command) == 1:
        return (command[0], [])
    (command, arguments) = command
    args = [""]
    paren = 0
    while len(arguments) > 0:
        c = arguments[0]
        arguments = arguments[1:]
        if c == '(':
            paren += 1
        elif c == ')':
            paren -= 1
            if paren < 0:
                raise RuntimeError("Unmatched closing brace in SMT output")
        elif c == " ":
            if paren == 0:
                arguments = arguments.strip()
                args.append("")
                continue
        args[-1] += c
    if not args[-1]:
        # Do not end with empty string
        args = args[:-1]

    return (command, args)
