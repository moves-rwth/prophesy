import logging
from prophesy.smt.smtlib import SmtlibSolver, parse_smt_expr

logger = logging.getLogger(__name__)


class YicesCLISolver(SmtlibSolver):
    """
    Yices 2 (cli) wrapper class
    """
    def __init__(self, location=None, memout=None, timeout=None):
        """
        
        :param location: If None, the configuration is queried.
        :param memout: If None, the configuration is queried
        :param timeout: If None, the configuration is queried
        """
        # Do not load before, configuration might change.
        from prophesy.config import configuration
        super().__init__(location if location is not None else configuration.get_yices(),
                         memout if memout is not None else configuration.get_smt_memout(),
                         timeout if timeout is not None else configuration.get_smt_timeout(), False)

    def name(self):
        return "Yices cli tool"

    def _additional_args(self):
        return []

    def _hard_timeout_option(self):
        return "--timeout=" + str(int(self.timeout))

    def _memout_option(self):
        return []

    def _read_model(self):
        output = ""
        i = 0
        for line in iter(self.process.stdout.readline, ""):
            if self.process.poll() is not None:
                break
            output += line.rstrip() + " "
            i += 1
            if i == self.nr_variables:
                break
        return output

    def _build_model(self, output):
        model = {}
        assignmentlist = [""]
        indentlvl = 0
        for c in output:
            if c == '(':
                indentlvl += 1
                assignmentlist[-1] += c
            elif c == ")":
                indentlvl -= 1
                assignmentlist[-1] += c
                if indentlvl == 0:
                    assignmentlist.append("")
            else:
                assignmentlist[-1] += c
        logger.debug(assignmentlist)
        for assignment in assignmentlist:
            if assignment.strip() == "":
                continue
            assignment = assignment.strip()
            assignment = assignment[1:-1].strip()
            if assignment[0] != "=":
                raise RuntimeError("Expected equality")
            assignment_pair = assignment[1:].strip().split(None,1)
            logger.debug(assignment_pair)
            parsed_expr = parse_smt_expr(assignment_pair[1])
            model[assignment_pair[0]] = parsed_expr

        return model
