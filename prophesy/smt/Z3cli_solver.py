import config
from config import configuration
from smt.smtlib import SmtlibSolver

class Z3CliSolver(SmtlibSolver):
    def __init__(self, location=configuration.get(config.EXTERNAL_TOOLS, "z3"), memout=4000, timeout=10):
        super(Z3CliSolver, self).__init__(location, memout, timeout)

    def name(self):
        return "Z3 cli tool"
