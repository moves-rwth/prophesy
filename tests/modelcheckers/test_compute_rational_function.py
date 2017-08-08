from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.modelcheckers.stormpy import StormpyModelChecker
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.input.prismfile import PrismFile
from prophesy.input.pctlfile import PctlFile

from helpers.helper import get_example_path
from requires import *

tools = [
    require_storm()(StormModelChecker),
    # require_prism(rational_function=True)(PrismModelChecker),
    require_stormpy()(StormpyModelChecker),
]


@pytest.mark.parametrize("MCType", tools)
def test_compute_rational_function(MCType):
    tool = MCType()
    prism_file = PrismFile(get_example_path("pdtmc", "funny_defined", "fun.pm"))
    pctl_file = PctlFile(get_example_path("pdtmc", "funny_defined", "property1.pctl"))
    tool.load_model_from_prismfile(prism_file)
    tool.set_pctl_formula(pctl_file.get(0))

    result = tool.get_rational_function()
    parameters = result.parameters
    assert parameters.get_variable("p")
    assert parameters.get_variable("q")
    ratfunc = result.ratfunc
    assert "q+p" in str(ratfunc)
