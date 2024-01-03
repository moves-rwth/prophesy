import subprocess
import functools
import logging

from prophesy.config import configuration
from prophesy.smt.smt import SMTSolver, Answer, VariableDomain
from prophesy.adapter.pycarl import Rational

logger = logging.getLogger(__name__)


def _smtfile_header():
    """
    smtlib header that describes the file.
    
    :return: string with the description
    """
    formula = "(set-logic QF_NRA)\n"
    formula += "(set-info :source |\n"
    formula += "Probabilistic verification" + "\n"
    formula += "prophesy" + "\n"
    formula += "|)\n"
    formula += "(set-info :smt-version 2.0)\n"
    formula += "(set-info :category \"industrial\")\n"
    return formula


class SmtlibSolver(SMTSolver):
    """
    Abstract class for smt-lib based command line interfaces for SMT solvers.
    """

    def __init__(self, location, memout, timeout, incremental=True):
        self.location = location
        self.formula = _smtfile_header()
        self.process = None
        self.string = self.formula
        self.memout = memout  # Mem limit in Mbyte
        self.timeout = timeout  # Soft timeout in seconds
        self.status = [""]
        self.exit_stored = True
        self.incremental = incremental
        self.nr_variables = 0
        self._fixed_guards = dict()
        self._guards = [set()]
        self.allow_names = False

    def _write(self, data):
        # Function to write+flush stdin, which may close after issuing a command
        stdin = self.process.stdin
        if stdin is not None:
            try:
                #("Write %s", data)
                stdin.write(data)
                stdin.flush()
            except:
                # Ignore the error, process will die on its own
                pass

    def _additional_args(self):
        return []

    def _hard_timeout_option(self):
        return ""

    def _memout_option(self):
        return [""]

    def _call_process(self, args):
        self.process = subprocess.Popen(args, stdout=subprocess.PIPE, stdin=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, universal_newlines=True)

    def run(self):
        if self.process is None:
            args = [self.location, self._hard_timeout_option()]
            args += self._memout_option()
            args += self._additional_args()
            self._call_process(args)
            if self.incremental:
                self._write(self.formula)
                self._write("".join(self.status))

        else:
            raise RuntimeError("The solver can only be started once")

    def stop(self, store_exit=True):
        logger.debug("Stop solver (definitive: %s)", store_exit)
        if self.process is not None:
            if store_exit:
                self.string += "(exit)\n"
            else:
                self.exit_stored = False
            self._write("(exit)\n")
            self.process.terminate()
            self.process = None
        elif not self.exit_stored:
            self.string += "(exit)\n"
            self.exit_stored = True

    def name(self):
        return "smtlib-interface"

    def version(self):
        args = [self.location, "--version"]
        p = subprocess.Popen(args, stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.STDOUT,
                             universal_newlines=True)
        version = p.communicate()[0].rstrip()
        p.terminate()
        return version

    def check(self):
        assert len(self._guards[-1]) == 0, "Guards {} not set".format(self._guards)
        assert self.process is not None
        if not self.incremental:
            self._write(self.formula)
            self._write("".join(self.status))
        s = "(check-sat)\n"
        self.string += s
        logger.debug("Call %s with timeout %s", self.name(), self.timeout)
        self._write(s)

        for line in iter(self.process.stdout.readline, ""):
            if not line and self.process.poll() is not None:
                break
            output = line.rstrip()
            if output == "":
                continue
            logger.debug("SMT result:\t" + output)
            if output == "unsat":
                if not self.incremental:
                    self.stop()
                    self.run()
                return Answer.unsat
            elif output == "sat":
                if not self.incremental:
                    self.stop()
                    self.run()
                return Answer.sat

            elif output == "unknown":
                if not self.incremental:
                    self.stop()
                    self.run()
                return Answer.unknown
            elif output == '(error "out of memory")':
                self.stop()
                self.run()
                logger.debug("Memory out with: {}".format(self.memout))
                return Answer.memout
            elif output == "Killed":
                self.stop()
                self.run()
                return Answer.killed
            elif output == "timeout":
                self.stop(False)
                self.run()
                return Answer.timeout
            else:
                self.stop()
                self.run()
                raise NotImplementedError("Unknown output '{}'. Input:\n{}".format(output, self.string))

        self.stop()
        self.run()
        return Answer.killed

    def push(self):
        logger.debug("Push [%s]", len(self.status))

        s = "(push)\n"
        self.string += s
        if self.incremental:
            self._write(s)
            self.status.append(s)
        else:
            self.status.append("")
        current_open_guards = self._guards[-1]
        self._guards.append(set(current_open_guards))

    def pop(self):
        logger.debug("Pop [%s]: %s", len(self.status), self.status[-1], )
        self.status.pop()
        s = "(pop)\n"
        self.string += s
        if self.incremental:
            self._write(s)
        self._guards.pop()

    def add_variable(self, symbol, domain=VariableDomain.Real):
        """Declare variable as a constant function with given domain.

        `symbol` must be a string, not a Variable object or similar.
        """
        assert isinstance(symbol, str)
        self.nr_variables += 1
        s = "(declare-fun " + symbol + " () " + domain.name + ")\n"
        self.string += s
        if self.incremental:
            self._write(s)
        self.status[-1] += s

    def assert_constraint(self, constraint, name=None):
        name_decl = ":named {})".format(name) if name and self.allow_names else ""
        name_opening = "(! " if name and self.allow_names else ""
        s = "(assert {}".format(name_opening) + constraint.to_smt2() + " {})\n".format(name_decl)
        self.string += s
        if self.incremental:
            self._write(s)
        self.status[-1] += s

    def assert_guarded_constraint(self, guard, constraint, name=None):
        name_decl = ":named {}".format(name) if name and self.allow_names else ""
        name_opening = "(! " if name and self.allow_names else ""
        if guard in self._fixed_guards:
            if self._fixed_guards[guard]:
                s = "(assert {}".format(name_opening) + constraint.to_smt2() + " {})\n".format(name_decl)
            else:
                return
        else:
            s = "(assert (=> " + guard + " {}".format(name_opening) + constraint.to_smt2() + " {}))\n".format(name_decl)
            self._guards[-1].add(guard)
        self.string += s
        if self.incremental:
            self._write(s)
        self.status[-1] += s

    def set_guard(self, guard, value):
        if value:
            s = "(assert " + guard + " )\n"
        else:
            s = "(assert (not " + guard + " ))\n"
        self._guards[-1].remove(guard)
        self.string += s
        if self.incremental:
            self._write(s)
        self.status[-1] += s

    def fix_guard(self, guard, value):
        assert guard not in self._fixed_guards
        self._fixed_guards[guard] = value
        self._guards[-1].add(guard)# Cheaper than checking in set_guard.
        self.set_guard(guard, value)


    def _build_model(self, output):
        raise NotImplementedError("General case not implemented")

    def _read_model(self):
        output = ""
        for line in iter(self.process.stdout.readline, ""):
            if self.process.poll() is not None:
                break
            output += line.rstrip()
            if output.count('(') == output.count(')'):
                break
        return output

    def get_model(self):
        s = "(get-model)\n"
        self.string += s
        self._write(s)
        output = self._read_model()
        logger.debug("** model result:\t" + output)
        try:
            model = self._build_model(output)
        except ValueError as e:
            print(e)
            model = None
            logger.warning("Cannot construct model exactly.")
            #TODO support approx.?

        return model

    def from_file(self, path):
        raise NotImplementedError

    def to_file(self, path):
        with open(path, 'w') as f:
            f.write(self.string)

    def print_calls(self):
        print(self.string)


def parse_smt_expr(expr):
    """Calculates given SMT expression "(OP ARG ARG)" as ARG OP ARG.
    Expression may be of arbitrary arity"""
    (cmd, args) = parse_smt_command(expr)
    args = map(parse_smt_expr, args)
    if cmd == "+":
        return functools.reduce(lambda x, y: x + y, args, 0)
    elif cmd == "-":
        return functools.reduce(lambda x, y: x - y, args, 0)
    elif cmd == "*":
        return functools.reduce(lambda x, y: x * y, args, 1)
    elif cmd == "/":
        return functools.reduce(lambda x, y: x / y, args)
    elif cmd == "true":
        return True
    elif cmd == "false":
        return False
    elif cmd == "root-obj":
        raise ValueError("root-obj cannot be translated into a rational.")
    else:
        return Rational(cmd)


def parse_smt_command(command):
    """Breaks the given SMT command "(CMD ARG ARG ARG)" into tuple (CMD, [ARG]),
    where ARG again can be a (non-parsed) command"""
    command = command.strip()
    if command[0] != "(":
        return command, []
    if command[-1] != ")":
        raise RuntimeError(f"Expected closing parenthesis at end of SMT output '{command}'.")
    # remove parenthesis
    command = command[1:-1].strip()
    arguments = None
    if command[0] == "(":
        arguments = command
        command = ""
    else:
        command = command.split(maxsplit=1)
        if len(command) == 1:
            return command[0], []
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
                raise RuntimeError(f"Unmatched closing parenthesis in SMT output '{arguments}'.")
        elif c == " ":
            if paren == 0:
                arguments = arguments.strip()
                args.append("")
                continue
        args[-1] += c
    if not args[-1]:
        # Do not end with empty string
        args = args[:-1]

    return command, args
