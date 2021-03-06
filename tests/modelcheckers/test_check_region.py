from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.modelcheckers.stormpy import StormpyModelChecker
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.input.modelfile import PrismFile
from prophesy.input.pctlfile import PctlFile
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.regions.region_checker import RegionCheckResult
from prophesy.data.constant import parse_constants_string

from helpers.helper import get_example_path
from requires import *

tools = [
    pytest.param(StormModelChecker, "storm", marks=[require_storm()]),
    # pytest.param(PrismModelChecker, "prism", marks=[require_prism(rational_function=True)]),
    pytest.param(StormpyModelChecker, "stormpy", marks=[require_stormpy()]),
]


@pytest.mark.parametrize("MCType,name", tools)
def test_check_hyperrectangle(MCType, name):
    tool = MCType()
    prism_file = PrismFile(get_example_path("brp", "brp.pm"))
    pctl_file = PctlFile(get_example_path("brp", "property1.pctl"))
    constants = parse_constants_string("N=16,MAX=2")
    tool.load_model_from_prismfile(prism_file, constants)
    tool.set_pctl_formula(pctl_file.get(0))

    hyperrectangle = HyperRectangle.from_region_string("0.25<=pL<=0.5,0.25<=pK<=0.5", prism_file.parameters)
    result = tool.check_hyperrectangle(prism_file.parameters, hyperrectangle, 0.7, True)
    assert len(result) == 1
    for res, region in result:
        assert res == RegionCheckResult.Satisfied

    hyperrectangle = HyperRectangle.from_region_string("0.5<=pL<=0.7,0.5<=pK<=0.7", prism_file.parameters)
    result = tool.check_hyperrectangle(prism_file.parameters, hyperrectangle, 0.7, True)
    for res, region in result:
        assert res == RegionCheckResult.Satisfied
