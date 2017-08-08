from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.modelcheckers.stormpy import StormpyModelChecker
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.input.prismfile import PrismFile
from helpers.helper import get_example_path
from requires import *

tools = [
    require_storm()(StormpyModelChecker),
    require_prism(rational_function=True)(PrismModelChecker),
    require_stormpy()(StormpyModelChecker),
]


@pytest.mark.parametrize("MCType", tools)
def test_compute_rational_function(MCType):
    tool = MCType()
    prism_file = PrismFile(get_example_path("pdtmc", "brp", "brp_16-2.pm"))
    tool.load_model_from_prismfile(prism_file)
    assert tool.prismfile is not None
    assert tool.constants is not None
