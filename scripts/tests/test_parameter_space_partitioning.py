import os.path
import pytest
import logging
from requires import *
from conftest import EXAMPLE_FOLDER, current_time
import click.testing

logger = logging.getLogger(__name__)
import compute_solutionfunction

benchmarks_smt = [
    require_z3()(("kydie", "kydie", "", "property1", "kydie", "15/100", "z3", "quads")),
    require_z3()(("nand", "nand", "N=2,K=1", "property1", "nand_2-1", "35/100", "z3", "quads")),
    require_yices()(("kydie", "kydie", "", "property1", "kydie", "15/100", "yices", "quads")),
    require_z3()(("kydie", "kydie", "", "property1", "kydie", "15/100", "z3", "rectangles")),
    require_z3()(("nand", "nand", "N=2,K=1", "property1", "nand_2-1", "35/100", "z3", "rectangles")),
    require_yices()(("kydie", "kydie", "", "property1", "kydie", "15/100", "yices", "rectangles")),

    # require_z3()(("brp", "brp_16-2","property1", 0.95, "z3", "quads")),
    # ("crowds", "crowds_3-5", 0.5, "z3"),
    #  ("nand", "nand_10-1", 0.1, "z3", "quads"),
    # ("crowds", "crowds_5-5", 0.5, "z3"),
    # ("crowds", "crowds_10-5", 0.5, "z3"),
    # ("nand", "nand_10-2", 0.8, "z3"),
    # ("nand-reward", "nand_10-1", 0.8, "z3"),
    # ("crowds", "crowds_15-5", 0.5, "z3"),
    # ("nand", "nand_10-5", 0.7, "z3"),
    # ("nand-reward", "nand_10-5", 0.7, "z3"),
    # ("crowds", "crowds_20-5", 0.6, "z3"),
    # ("nand", "nand_20-2", 0.3, "z3"),
    # ("nand-reward", "nand_20-2", 0.4, "z3"),
    #   ("nand", "nand_20-5", "z3"),
    #   ("nand-reward", "nand_20-5", "z3"),
    #   ("brp", "brp_128-2", "z3"),
    #   ("brp", "brp_128-5", "z3"),
    #   ("brp", "brp_256-2", "z3"),
    #   ("brp", "brp_256-5", "z3"),
]


@pytest.mark.parametrize("name,file,constants,propertyfile,ratfile,threshold,tool,method",
                         benchmarks_smt)
def test_script_sfsmt(name, file, constants, propertyfile, ratfile, threshold, tool, method):
    END_CRITERIA = "--area"
    END_CRITERIA_VALUE = 0.30

    command = [
        "--solver={}".format(tool),
        "load_solution_function",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.rat".format(name, ratfile)),
        "set_threshold",
        str(threshold),
        "load_samples",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.samples".format(name, ratfile)),
        "parameter_space_partitioning",
        END_CRITERIA,
        str(END_CRITERIA_VALUE),
        "sfsmt",
        method
    ]

    logger.debug("parameter_synthesis.py " + " ".join(command))
    runner = click.testing.CliRunner()
    try:
        result = runner.invoke(compute_solutionfunction.parameter_synthesis, command)
    except NotImplementedError:
        pytest.xfail()
    assert result.exit_code == 0, result.output



benchmarks_etr = [
    require_z3()(("kydie", "kydie", "", "property1", "kydie", "15/100", "z3", "quads")),
    require_z3()(("nand", "nand", "N=2,K=1", "property1", "nand_2-1", "35/100", "z3", "quads")),
    require_yices()(("kydie", "kydie", "", "property1", "kydie", "15/100", "yices", "quads")),
    require_z3()(("kydie", "kydie", "", "property1", "kydie", "15/100", "z3", "rectangles")),
    require_z3()(("nand", "nand", "N=2,K=1", "property1", "nand_2-1", "35/100", "z3", "rectangles")),
    require_yices()(("kydie", "kydie", "", "property1", "kydie", "15/100", "yices", "rectangles")),

    # require_z3()(("brp", "brp_16-2","property1", 0.95, "z3", "quads")),
    # ("crowds", "crowds_3-5", 0.5, "z3"),
    #  ("nand", "nand_10-1", 0.1, "z3", "quads"),
    # ("crowds", "crowds_5-5", 0.5, "z3"),
    # ("crowds", "crowds_10-5", 0.5, "z3"),
    # ("nand", "nand_10-2", 0.8, "z3"),
    # ("nand-reward", "nand_10-1", 0.8, "z3"),
    # ("crowds", "crowds_15-5", 0.5, "z3"),
    # ("nand", "nand_10-5", 0.7, "z3"),
    # ("nand-reward", "nand_10-5", 0.7, "z3"),
    # ("crowds", "crowds_20-5", 0.6, "z3"),
    # ("nand", "nand_20-2", 0.3, "z3"),
    # ("nand-reward", "nand_20-2", 0.4, "z3"),
    #   ("nand", "nand_20-5", "z3"),
    #   ("nand-reward", "nand_20-5", "z3"),
    #   ("brp", "brp_128-2", "z3"),
    #   ("brp", "brp_128-5", "z3"),
    #   ("brp", "brp_256-2", "z3"),
    #   ("brp", "brp_256-5", "z3"),
]



@pytest.mark.parametrize("name,file,constants,propertyfile,ratfile,threshold,tool,method", benchmarks_etr)
def test_script_etr(name, file, constants, propertyfile, ratfile, threshold, tool, method):
    END_CRITERIA = "--area"
    END_CRITERIA_VALUE = 0.30

    command = [
        "--solver={}".format(tool),
        "load_problem",
        "--constants",
        constants,
        os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
        os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, propertyfile)),
        "load_solution_function",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.rat".format(name, ratfile)),
        "set_threshold",
        str(threshold),
        "load_samples",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.samples".format(name, ratfile)),
        "parameter_space_partitioning",
        END_CRITERIA,
        str(END_CRITERIA_VALUE),
        "etr",
        method
    ]

    logger.debug("parameter_synthesis.py " + " ".join(command))
    runner = click.testing.CliRunner()
    try:
        result = runner.invoke(compute_solutionfunction.parameter_synthesis, command)
    except NotImplementedError:
        pytest.xfail()
    assert result.exit_code == 0, result.output

benchmarks_pla = [
    require_storm()(("brp", "brp", "N=16,MAX=2", "property1", "brp_16-2", 0.95, "storm", "quads")),
    require_storm()(("crowds", "crowds", "CrowdSize=3,TotalRuns=5", "property1", "crowds_3-5", 0.95, "storm", "quads")),
    require_storm()(("nand", "nand", "N=2,K=1", "property1", "nand_2-1", 0.35, "storm", "quads")),
    require_stormpy()(("brp", "brp", "N=16,MAX=2", "property1", "brp_16-2", 0.95, "stormpy", "quads")),
    require_storm()(("brp", "brp", "N=16,MAX=2", "property1", "brp_16-2", 0.95, "storm", "rectangles")),
    require_storm()(
        ("crowds", "crowds", "CrowdSize=3,TotalRuns=5", "property1", "crowds_3-5", 0.95, "storm", "rectangles")),
    require_storm()(("nand", "nand", "N=2,K=1", "property1", "nand_2-1", 0.35, "storm", "rectangles")),
    require_stormpy()(("brp", "brp", "N=16,MAX=2", "property1", "brp_16-2", 0.95, "stormpy", "rectangles")),
]



@pytest.mark.parametrize("name,file,constants,propertyfile,samplesfile,threshold,tool,method", benchmarks_pla)
def test_script_pla(name, file, constants, propertyfile, samplesfile, threshold, tool, method):
    END_CRITERIA = "--area"
    END_CRITERIA_VALUE = 0.30

    command = [
        "--solver=z3",
        "--mc={}".format(tool),
        "load_problem",
        "--constants",
        constants,
        os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
        os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, propertyfile)),
        "set_threshold",
        str(threshold),
        "load_samples",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.samples".format(name, samplesfile)),
        "parameter_space_partitioning",
        "--epsilon",
        "0.001",
        END_CRITERIA,
        str(END_CRITERIA_VALUE),
        "pla",
        method
    ]


    logger.debug("parameter_synthesis.py " + " ".join(command))
    runner = click.testing.CliRunner()
    try:
        result = runner.invoke(compute_solutionfunction.parameter_synthesis, command)
    except NotImplementedError:
        pytest.xfail()
    assert result.exit_code == 0, result.output
