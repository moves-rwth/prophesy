from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.modelcheckers.stormpy import StormpyModelChecker
from prophesy.input.modelfile import PrismFile
from prophesy.input.pctlfile import PctlFile
import prophesy.adapter.pycarl as pc
from prophesy.data.point import Point

from helpers.helper import get_example_path
from requires import *
import copy

tools = [
    require_storm()((StormModelChecker, "storm")),
    require_stormpy()((StormpyModelChecker, "stormpy")),
]


@pytest.mark.parametrize("MCType,name", tools)
def test_perform_sampling(MCType, name):
    tool = MCType()
    prism_file = PrismFile(get_example_path("funny_defined", "fun.pm"))
    pctl_file = PctlFile(get_example_path("funny_defined", "property1.pctl"))
    tool.load_model_from_prismfile(prism_file)
    tool.set_pctl_formula(pctl_file.get(0))

    parameters = copy.copy(prism_file.parameters)
    parameters.make_intervals_closed(pc.Rational(pc.Integer(1), pc.Integer(1000)))

    points = [(Point(pc.Rational(0.25), pc.Rational(0.5)))]
    sample_points = parameters.instantiate(points)
    assert len(sample_points) == 1
    result = tool.perform_sampling(sample_points)
    assert len(result) == 1
    for instantiation, val in result.items():
        assert val == pc.Rational(0.75)
