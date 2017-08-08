###
# Helpers for the script tests.
####

import pytest

from prophesy.config import configuration


def require_prism(rational_function=False):
    if rational_function:
        return pytest.mark.xfail()
    return pytest.mark.skipif(not configuration.get_prism(), reason="requires prism")


def require_stormpy():
    return pytest.mark.skipif(not configuration.has_stormpy(), reason="requires stormpy")


def require_storm():
    return pytest.mark.skipif(not configuration.get_storm(), reason="requires storm")


def require_z3():
    return pytest.mark.skipif(not configuration.get_z3(), reason="requires z3")


def require_yices():
    return pytest.mark.skipif(not configuration.get_yices(), reason="requires yices")
