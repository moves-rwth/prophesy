from prophesy import config
from prophesy.config import configuration
from prophesy.smt.smtlib import SmtlibSolver

class Z3CliSolver(SmtlibSolver):
    def __init__(self, location=configuration.get(config.EXTERNAL_TOOLS, "z3"), memout=4000, timeout=10):
        super().__init__(location, memout, timeout)

    def name(self):
        return "Z3 cli tool"
