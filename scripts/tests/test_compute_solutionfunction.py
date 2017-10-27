import os.path
import pytest
from requires import *
from conftest import EXAMPLE_FOLDER, current_time
import click.testing

import compute_solutionfunction

target_file = "compute_solutionfunction_{}.rat".format(current_time)

benchmarks = [
    require_storm()(("brp", "brp", "N=16,MAX=2", "property1", "storm")),
    require_prism(rational_function=True)(("brp", "brp", "N=16,MAX=2", "property1", "prism")),
    require_stormpy()(("brp", "brp", "N=16,MAX=2", "property1", "stormpy")),
]


@pytest.mark.parametrize("name,file,constants,property,tool", benchmarks)
def test_script(name, file, constants, property, tool):
    command = ["--mc={}".format(tool),
               "load_problem",
               "--constants",
               constants,
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, property)),
               "compute_solution_function",
               '--export',
               target_file
               ]
    runner = click.testing.CliRunner()
    result = runner.invoke(compute_solutionfunction.parameter_synthesis, command)
    assert result.exit_code == 0, result.output
    assert os.path.isfile(target_file)
    os.remove(target_file)
