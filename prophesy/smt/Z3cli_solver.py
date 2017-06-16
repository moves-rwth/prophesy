from prophesy.config import configuration
from prophesy.smt.smtlib import SmtlibSolver

class Z3CliSolver(SmtlibSolver):
    def __init__(self, location=configuration.get_z3(), memout=4000, timeout=configuration.get_smt_timeout()):
        super().__init__(location, memout, timeout)

    def name(self):
        return "Z3 cli tool"
