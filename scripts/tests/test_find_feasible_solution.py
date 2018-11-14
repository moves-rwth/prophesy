import os.path
import pytest
import logging
from conftest import EXAMPLE_FOLDER, current_time
from requires import *
import click.testing
import pycarl

import parameter_synthesis
logger = logging.getLogger(__name__)


target_file = "sampling_model_{}.samples".format(current_time)

benchmarks = [
    ("brp", "brp_16-2", 0.9, "above"),
    ("brp", "brp_16-2", 0.9, "below")

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


@pytest.mark.parametrize("name,benchmark,threshold,dir", benchmarks)
def test_script_sfsmt(name, benchmark, threshold, dir):
    command = ["load-solution-function",
               os.path.join(EXAMPLE_FOLDER, "{}/{}.rat".format(name, benchmark)),
               "set-threshold",
               str(threshold),
               "find-feasible-instantiation",
                dir,
                "sfsmt"
               ]
    logger.debug("parameter_synthesis.py " + " ".join(command))
    runner = click.testing.CliRunner()
    result = runner.invoke(parameter_synthesis.parameter_synthesis, command)
    assert result.exit_code == 0, result.output
    pycarl.clear_variable_pool()


benchmarks = [
    ("brp", "brp_16-2", "property1", 0.9, "above"),
    ("brp", "brp_16-2", "property1", 0.9, "below")

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

@require_stormpy()
@pytest.mark.parametrize("name,benchmark,property,threshold,dir", benchmarks)
def test_script_etr(name, benchmark,property, threshold, dir):
    command = ["load-problem",
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, benchmark)),
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, property)),
               "set-threshold",
               str(threshold),
               "find-feasible-instantiation",
                dir,
                "etr"
               ]
    logger.debug("parameter_synthesis.py " + " ".join(command))
    runner = click.testing.CliRunner()
    result = runner.invoke(parameter_synthesis.parameter_synthesis, command)
    assert result.exit_code == 0, result.output
    pycarl.clear_variable_pool()

@require_stormpy()
@require_gurobipy()
@pytest.mark.parametrize("name,benchmark,property,threshold,dir", benchmarks)
def test_script_qcqp(name, benchmark,property, threshold, dir):
    command = ["load-problem",
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, benchmark)),
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, property)),
               "set-threshold",
               str(threshold),
               "find-feasible-instantiation",
               "--qcqp-incremental",
               "--qcqp-store-quadratic",
               "--qcqp-handle-violation", "minimisation",
               "--qcqp-mc", "full",
               "--precheck-welldefinedness",
               dir,
                "qcqp"
               ]
    logger.debug("parameter_synthesis.py " + " ".join(command))
    runner = click.testing.CliRunner()
    result = runner.invoke(parameter_synthesis.parameter_synthesis, command)
    assert result.exit_code == 0, result.output
    pycarl.clear_variable_pool()

