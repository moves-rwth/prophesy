import os.path
import pytest
import logging
from requires import *
from conftest import EXAMPLE_FOLDER, current_time
import click.testing

import compute_solutionfunction
logger = logging.getLogger(__name__)

SAMPLINGNR = 3
ITERATIONS = 1

target_file = "sampling_model_{}.samples".format(current_time)

benchmarks = [
    require_storm()(("brp", "brp", "N=16,MAX=2", "property1", 0.9, "storm")),
    require_prism()(("brp", "brp", "N=16,MAX=2", "property1", 0.9, "prism")),
    # require_prism()(("brp", "brp", "N=16,MAX=2", "property1", 0.98, "prism")),
    require_stormpy()(("brp", "brp", "N=16,MAX=2", "property1", 0.9, "stormpy")),
    #   ("brp", "brp_128-2", 0.9, True),
    #   ("brp", "brp_128-5", 0.9, True),
    #   ("brp", "brp_256-2", 0.9, True),
    #   ("brp", "brp_256-5", 0.9, True),
    # ("crowds", "crowds_3-5", 0.9, True),
    # ("crowds", "crowds_3-5", 0.5, True),
    #   ("crowds", "crowds_5-5", 0.9, True),
    #   ("crowds", "crowds_10-5", 0.9, True),
    #   ("crowds", "crowds_15-5", 0.9, True),
    #   ("crowds", "crowds_20-5", 0.9, True),
    # ("nand", "nand_10-1", 0.1, True),
    # ("nand", "nand_10-1", 0.5, True),
    #   ("nand", "nand_10-2", 0.5, True),
    #   ("nand", "nand_10-5", 0.5, True),
    #   ("nand", "nand_20-2", 0.5, True),
    #   ("nand", "nand_20-5", 0.5, True),
    #   ("nand-reward", "nand_10-5", 0.5, True),
    #   ("nand-reward", "nand_20-2", 0.5, True),
    #   ("nand-reward", "nand_20-5", 0.5, True),
]

@pytest.mark.parametrize("name,file,constants,property,threshold,tool", benchmarks)
def test_script(name, file, constants, property, threshold, tool):
    command = ["--mc={}".format(tool),
               "load_problem",
               "--constants",
               constants,
               "--threshold",
               str(threshold),
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, property)),
               "sample",
               "--samplingnr",
               str(SAMPLINGNR),
               "--iterations",
               str(ITERATIONS),
               '--export',
               target_file
               ]
    logger.debug("parameter_synthesis.py " + " ".join(command))
    runner = click.testing.CliRunner()
    result = runner.invoke(compute_solutionfunction.parameter_synthesis, command)
    assert result.exit_code == 0, result.output
    assert os.path.isfile(target_file)
    os.unlink(target_file)
