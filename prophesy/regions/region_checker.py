from enum import Enum


class RegionCheckResult(Enum):
    sat = 0
    unsat = 1
    unknown = 2


class RegionChecker():
    def __init__(self):
        pass
