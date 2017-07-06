from enum import Enum


class RegionCheckResult(Enum):
    CounterExample = 0  #: The region does not satisfy the property; we found a counterexample
    Satisfied = 1       #: The region satisfies the property.
    Refined = 2         #: We don't know, we return a subregion which is still undecided. The remainder is satisfied.
    unknown = 3         #: We don't know.


class RegionChecker():
    """
    Interface for region checkers.
    """
    def __init__(self):
        pass

