import os.path
import pytest
import logging
from conftest import EXAMPLE_FOLDER, current_time
from requires import *
import click.testing

logger = logging.getLogger(__name__)
import parameter_synthesis
import pycarl

benchmarks_pipeline = [
    pytest.param("brp", "brp", "N=16,MAX=2", "property1", 0.7, "z3", "storm", "etr", "quads", marks=[pytest.mark.xfail, require_storm(), require_z3()]),
    pytest.param("brp", "brp", "N=16,MAX=2", "property1", 0.7, "z3", "stormpy", "etr", "quads", marks=[require_stormpy(), require_z3()]),
    pytest.param("brp", "brp", "N=16,MAX=2", "property1", 0.7, "z3", "storm", "pla", "quads", marks=[require_storm(), require_z3(), require_pycarl_parser()]),
    pytest.param("brp", "brp", "N=16,MAX=2", "property1", 0.7, "z3", "stormpy", "pla", "quads", marks=[require_stormpy(), require_z3()]),
    pytest.param("herman", "herman3", "", "herman", 0.4, "z3", "stormpy", "pla", "quads", marks=[require_stormpy(), require_z3()]),
]


@pytest.mark.parametrize("name,file,constants,propertyfile,threshold,solver,tool,verification_method,region_method",
                         benchmarks_pipeline)
def test_script_pla(name, file, constants, propertyfile, threshold, solver, tool, verification_method, region_method):
    command = [
        "--solver={}".format(solver),
        "--mc={}".format(tool),
        "load-problem",
        "--constants", constants,
        os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
        os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, propertyfile)),
        "set-threshold",
        str(threshold),
        "set-parameter-space",
        "--epsilon", "0.001",
        "sample",
        "parameter-space-partitioning",
        "--area", "0.30",
        verification_method,
        region_method
    ]

    logger.debug("parameter_synthesis.py " + " ".join(command))
    runner = click.testing.CliRunner()
    try:
        result = runner.invoke(parameter_synthesis.parameter_synthesis, command)
    except NotImplementedError:
        pytest.xfail()
    assert result.exit_code == 0, result.output
    pycarl.clear_variable_pool()
