import os.path
import pytest
from requires import *
from conftest import EXAMPLE_FOLDER, current_time

import compute_solutionfunction

target_file = "compute_solutionfunction_{}.rat".format(current_time)

benchmarks = [
    require_storm()(("brp", "brp", "N=16,MAX=2", "property1", "storm")),
    require_prism(rational_function=True)(("brp", "brp", "N=16,MAX=2", "property1", "prism")),
    require_stormpy()(("brp", "brp", "N=16,MAX=2", "property1", "stormpy")),
]


@pytest.mark.parametrize("name,file,constants,property,tool", benchmarks)
def test_script(name, file, constants, property, tool):
    command = ["--file",
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
               "--constants",
               constants,
               "--pctl-file",
               os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, property)),
               "--{}".format(tool),
               '--result-file',
               target_file
               ]
    compute_solutionfunction.run(command, False)
    assert os.path.isfile(target_file)
    os.remove(target_file)
