from prophesy.config import configuration
from prophesy.smt.smtlib import SmtlibSolver, parse_smt_command, parse_smt_expr


class Z3CliSolver(SmtlibSolver):
    """
    TODO: support the soft timeout kill.
    """
    def __init__(self, location=configuration.get_z3(), memout=4000, timeout=configuration.get_smt_timeout()):
        super().__init__(location, memout, timeout, True)

    def name(self):
        return "Z3 cli tool"

    def _additional_args(self):
        return ["-smt2", "-in"]

    def _hard_timeout_option(self):
        return "-T:" + str(self.timeout)

    def _memout_option(self):
        return ["-memory:" + str(self.memout)]

    def _build_model(self, output):
        model = {}
        (cmd, model_cmds) = parse_smt_command(output)
        if cmd == "error":
            raise RuntimeError("SMT Error in get_model(). Input:\n{}".format(self.string))
        for cmd in model_cmds:
            (_, args) = parse_smt_command(cmd)
            if args[2] == "Real":
                model[args[0]] = parse_smt_expr(args[3])
        return model
