from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.modelcheckers.stormpy import StormpyModelChecker
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.input.prismfile import PrismFile
from prophesy.input.pctlfile import PctlFile
import prophesy.adapter.pycarl as pc
from prophesy.data.samples import ParameterInstantiations
from prophesy.data.point import Point

from helpers.helper import get_example_path
from requires import *
import copy

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

    parameters = copy.deepcopy(prism_file.parameters)
    parameters.make_intervals_closed(pc.Rational(pc.Integer(1), pc.Integer(1000)))

    points = [(Point(pc.Rational(0.25), pc.Rational(0.5)))]
    sample_points = ParameterInstantiations.from_points(points, parameters)
    assert len(sample_points) == 1
    result = tool.perform_sampling(sample_points)
    assert len(result) == 1
    for instantiation, val in result:
        assert val == pc.Rational(0.75)

