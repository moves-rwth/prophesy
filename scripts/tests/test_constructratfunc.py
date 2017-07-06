import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import prismfiletoratfunc
import pytest
import time
from tests import requires
from requires import *

EXAMPLE_FOLDER = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                              "benchmarkfiles/pdtmc")

current_time = time.strftime("%H_%M", time.localtime())
target_file = "buildratfunc_{}".format(current_time)


benchmarks = [
    require_storm()(("brp", "brp_16_2", "property1", "storm")),
    require_prism(rational_function=True)(("brp", "brp_16_2", "property1", "prism")),
    require_stormpy()(("brp", "brp_16_2", "property1", "stormpy")),
]

@pytest.mark.parametrize("name,file,property,tool", benchmarks)
def test_script(name, file, property, tool):
    command = ["--file",
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
               "--pctl-file",
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, property)),
               "--{}".format(tool),
               '--result-file',
               target_file
               ]
    prismfiletoratfunc.run(command, False)
    os.remove(target_file)