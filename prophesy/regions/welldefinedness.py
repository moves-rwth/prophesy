import logging
from enum import Enum
from prophesy.smt.smt import Answer
import prophesy.adapter.pycarl as pc

logger = logging.getLogger(__name__)


class WelldefinednessResult(Enum):
    Welldefined = 0
    Undecided = 1
    Illdefined = 2


def check_welldefinedness(checker, parameters, region, constraints):
        """
        
        :param checker: 
        :param parameters: 
        :param region: 
        :param constraints: 
        :rtype: WelldefinednessResult
        :return: 
        """
        for v in parameters.get_variables():
            checker.add_variable(v)
        checker.assert_constraint(region.to_formula(parameters.get_variables()))
        welldefinedness = pc.Constraint(True)
        checker.push()
        for c in constraints:
            welldefinedness = (welldefinedness & c)
        checker.assert_constraint(~welldefinedness)
        result = checker.check()
        if result == Answer.sat:
            logger.debug("Part of the region is ill-defined.")
            checker.pop()
            checker.assert_constraint(welldefinedness)
            result = checker.check()
            if result == Answer.sat:
                logger.debug("Region is neither well- nor ill-defined.")
                return WelldefinednessResult.Undecided
            elif result == Answer.unsat:
                logger.debug("Region is ill-defined.")
                return WelldefinednessResult.Illdefined
        elif result == Answer.unsat:
            logger.debug("Region is well-defined.")
            return WelldefinednessResult.Welldefined
        elif result == Answer.unknown:
            raise RuntimeError("Unknown answers for well-definedness-checks are currently not supported")
