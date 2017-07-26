import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import sampling_model
import pytest
import time
from tests import requires
from requires import *

EXAMPLE_FOLDER = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                              "benchmarkfiles/pdtmc")
SAMPLINGNR = 3
ITERATIONS = 1

current_time = time.strftime("%H_%M", time.localtime())
target_file = "modelsampling_{}.samples".format(current_time)


benchmarks = [
    require_storm()(("brp", "brp_16-2", "property1", 0.9, "storm")),
    require_prism()(("brp", "brp_16-2", "property1", 0.9, "prism")),
    require_prism()(("brp", "brp_16-2", "property1", 0.98, "prism")),
    require_stormpy()(("brp", "brp_16-2", "property1", 0.9, "stormpy")),
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


@pytest.mark.parametrize("name,file,property,threshold,tool", benchmarks)
def test_script(name, file, property, threshold,tool):
    command = ["--file",
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
               "--pctl-file",
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, property)),
               "--samplingnr",
               str(SAMPLINGNR),
               "--iterations",
               str(ITERATIONS),
               "--threshold",
               str(threshold),
               "--{}".format(tool),
               '--samples-file',
               target_file
               ]
    sampling_model.run(command, False)
    os.unlink(target_file)
