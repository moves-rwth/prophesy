
import subprocess
import time

import sys
import os
import pytest
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import buildconstraints

EXAMPLE_FOLDER = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                              "benchmarkfiles/examples")

current_time = time.strftime("%H_%M", time.localtime())
target_file = "constraint_generation_{}".format(current_time)

benchmarks = [
    ("brp", "brp_16-2", 0.95, "z3", "quads"),
    ("brp", "brp_16-2", 0.95, "yices", "quads"),
    # ("crowds", "crowds_3-5", 0.5, "z3"),
  #  ("nand", "nand_10-1", 0.1, "z3", "quads"),
    #("crowds", "crowds_5-5", 0.5, "z3"),
    #("crowds", "crowds_10-5", 0.5, "z3"),
    #("nand", "nand_10-2", 0.8, "z3"),
    #("nand-reward", "nand_10-1", 0.8, "z3"),
    #("crowds", "crowds_15-5", 0.5, "z3"),
    #("nand", "nand_10-5", 0.7, "z3"),
    #("nand-reward", "nand_10-5", 0.7, "z3"),
    #("crowds", "crowds_20-5", 0.6, "z3"),
    #("nand", "nand_20-2", 0.3, "z3"),
    #("nand-reward", "nand_20-2", 0.4, "z3"),
#   ("nand", "nand_20-5", "z3"),
#   ("nand-reward", "nand_20-5", "z3"),
#   ("brp", "brp_128-2", "z3"),
#   ("brp", "brp_128-5", "z3"),
#   ("brp", "brp_256-2", "z3"),
#   ("brp", "brp_256-5", "z3"),
]

@pytest.mark.parametrize("name,file,threshold,tool,method", benchmarks)
def test_script(name, file, threshold, tool, method):
    THRESHOLD_AREA = 0.001
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
                END_CRITERIA,
                str(END_CRITERIA_VALUE),
                "--{}".format(method),
                ]
    buildconstraints.run(command, False)
