import os.path
import pytest
import logging
from conftest import EXAMPLE_FOLDER, current_time
from requires import *
import click.testing
import pycarl

import parameter_synthesis
logger = logging.getLogger(__name__)

target_file = "compute_solutionfunction_{}.rat".format(current_time)

benchmarks = [
    pytest.param("brp", "brp", "N=16,MAX=2", "property1", "storm", marks=[require_storm(),require_pycarl_parser()]),
    pytest.param("brp", "brp", "N=16,MAX=2", "property1", "prism", marks=[require_prism(rational_function=True)]),
    pytest.param("brp", "brp", "N=16,MAX=2", "property1", "stormpy", marks=[require_stormpy()]),
]


@pytest.mark.parametrize("name,file,constants,property,tool", benchmarks)
def test_script(name, file, constants, property, tool):
    command = ["--mc={}".format(tool),
               "load-problem",
               "--constants",
               constants,
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, property)),
               "compute-solution-function",
               '--export',
               target_file
               ]
    runner = click.testing.CliRunner()
    logger.debug("parameter_synthesis.py " + " ".join(command))
    result = runner.invoke(parameter_synthesis.parameter_synthesis, command)
    assert result.exit_code == 0, result.output
    assert os.path.isfile(target_file)
    os.remove(target_file)
    pycarl.clear_variable_pool()
