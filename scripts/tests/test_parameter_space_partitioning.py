import os.path
import pytest
from requires import *
from conftest import EXAMPLE_FOLDER, current_time

import parameter_space_partitioning

benchmarks_smt = [
    require_z3()(("kydie", "kydie", "property1", "15/100", "z3", "quads")),
    require_z3()(("brp", "brp_16-2", "property1", "85/100", "z3", "quads")),
    require_yices()(("kydie", "kydie", "property1", "15/100", "yices", "quads"))

    #require_z3()(("brp", "brp_16-2","property1", 0.95, "z3", "quads")),
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


@pytest.mark.parametrize("name,file,propertyfile,threshold,tool,method", benchmarks_smt)
def test_script_sfsmt(name, file, propertyfile, threshold, tool, method):
    END_CRITERIA = "--area"
    END_CRITERIA_VALUE = 0.30

    command = [
        "--rat-file",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.rat".format(name, file)),
        "--samples-file",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.samples".format(name, file)),
        "--{}".format(tool),
        "--threshold",
        str(threshold),
        "--sfsmt",
        END_CRITERIA,
        str(END_CRITERIA_VALUE),
        "--{}".format(method),
    ]
    parameter_space_partitioning.run(command, False)

@pytest.mark.parametrize("name,file,propertyfile,threshold,tool,method", benchmarks_smt)
def test_script_etr(name, file, propertyfile, threshold, tool, method):
    END_CRITERIA = "--area"
    END_CRITERIA_VALUE = 0.30

    command = [
        "--model-file",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
        "--property-file",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, propertyfile)),
        "--rat-file",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.rat".format(name, file)),
        "--samples-file",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.samples".format(name, file)),
        "--{}".format(tool),
        "--threshold",
        str(threshold),
        "--etr",
        END_CRITERIA,
        str(END_CRITERIA_VALUE),
        "--{}".format(method),
    ]
    parameter_space_partitioning.run(command, False)


benchmarks_pla = [
    require_storm()(("brp", "brp_16-2", "property1", 0.95, "storm", "quads")),
    require_storm()(("crowds", "crowds_3-5", "property1", 0.95, "storm", "quads")),
    require_stormpy()(("brp", "brp_16-2", "property1", 0.95, "stormpy", "quads")),
]


@pytest.mark.parametrize("name,file,propertyfile,threshold,tool,method", benchmarks_pla)
def test_script_pla(name, file, propertyfile, threshold, tool, method):
    END_CRITERIA = "--area"
    END_CRITERIA_VALUE = 0.30

    command = [
        "--model-file",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
        "--property-file",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, propertyfile)),
        "--samples-file",
        os.path.join(EXAMPLE_FOLDER, "{}/{}.samples".format(name, file)),
        "--{}".format(tool),
        "--pla",
        "--threshold",
        str(threshold),
        "--z3",
        END_CRITERIA,
        str(END_CRITERIA_VALUE),
        "--{}".format(method),
    ]
    parameter_space_partitioning.run(command, False)
