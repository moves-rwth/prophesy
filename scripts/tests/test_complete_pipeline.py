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
    pytest.mark.xfail()(
        require_storm()(require_z3()(("brp", "brp", "N=16,MAX=2", "property1", 0.7, "z3", "storm", "etr", "quads")))),
    require_stormpy()(require_z3()(("brp", "brp", "N=16,MAX=2", "property1", 0.7, "z3", "stormpy", "etr", "quads"))),
    require_storm()(require_z3()(("brp", "brp", "N=16,MAX=2", "property1", 0.7, "z3", "storm", "pla", "quads"))),
    require_stormpy()(require_z3()(("brp", "brp", "N=16,MAX=2", "property1", 0.7, "z3", "stormpy", "pla", "quads"))),

    require_stormpy()(require_z3()(("herman", "herman3", "", "herman", 0.4, "z3", "stormpy", "pla", "quads"))),
]


@pytest.mark.parametrize("name,file,constants,propertyfile,threshold,solver,tool,verification_method,region_method",
                         benchmarks_pipeline)
def test_script_pla(name, file, constants, propertyfile, threshold, solver, tool, verification_method, region_method):
    command = [
        "--solver={}".format(solver),
        "--mc={}".format(tool),
        "load_problem",
        "--constants", constants,
        os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
        os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, propertyfile)),
        "set_threshold",
        str(threshold),
        "sample",
        "parameter_space_partitioning",
        "--epsilon", "0.001",
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
