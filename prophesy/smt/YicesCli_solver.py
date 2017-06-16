from prophesy.config import configuration
from prophesy.smt.smtlib import SmtlibSolver

class YicesCLISolver(SmtlibSolver):
    def __init__(self, location=configuration.get_z3(), memout=4000, timeout=configuration.get_smt_timeout()):
        super().__init__(location, memout, timeout)

    def name(self):
        return "Yices cli tool"
