import os.path
import pytest
import logging
from requires import *
from conftest import EXAMPLE_FOLDER, current_time
import click.testing

import parameter_synthesis
logger = logging.getLogger(__name__)


target_file = "sampling_model_{}.samples".format(current_time)

benchmarks = [
    require_stormpy()(("brp", "brp", "N=16,MAX=2", "property1", "stormpy"))

]

@pytest.mark.parametrize("name,file,constants,property,tool", benchmarks)
def test_script(name, file, constants, property, tool):
    command = ["--mc={}".format(tool),
               "load-problem",
               "--constants",
               constants,
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, property)),
               "search-optimum",
                "max"
               ]
    logger.debug("parameter_synthesis.py " + " ".join(command))
    runner = click.testing.CliRunner()
    result = runner.invoke(parameter_synthesis.parameter_synthesis, command)
    assert result.exit_code == 0, result.output
