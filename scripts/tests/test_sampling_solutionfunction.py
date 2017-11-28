import os.path
import logging
import pytest
from requires import *
from conftest import EXAMPLE_FOLDER, current_time
import click.testing

logger = logging.getLogger(__name__)
import parameter_synthesis

SAMPLINGNR = 3
ITERATIONS = 1

target_file = "sampling_solutionfunction_{}.samples".format(current_time)

benchmarks = [
    ("brp", "brp_16-2", 0.9, False),
    #   ("brp", "brp_16-2", 0.5, True),
    #    ("brp", "brp_16-2", 0.98, True),
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
    #  ("nand-reward", "nand_10-2", 0.5, True),
    #   ("nand-reward", "nand_10-5", 0.5, True),
    #   ("nand-reward", "nand_20-2", 0.5, True),
    #   ("nand-reward", "nand_20-5", 0.5, True),
]


@pytest.mark.parametrize("name,benchmark,threshold,safe_above", benchmarks)
def test_script(name, benchmark, threshold, safe_above):
    command = ["load_solution_function",
               os.path.join(EXAMPLE_FOLDER, "{}/{}.rat".format(name, benchmark)),
               "set_threshold",
               str(threshold),
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
    result = runner.invoke(parameter_synthesis.parameter_synthesis, command)
    assert result.exit_code == 0, result.output
    assert os.path.isfile(target_file)
    os.unlink(target_file)


