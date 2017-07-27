import os.path
import pytest
from requires import *
from conftest import MODEL_FOLDER, current_time

import compute_solutionfunction

target_file = "compute_solutionfunction_{}.rat".format(current_time)

benchmarks = [
    require_storm()(("brp", "brp_16-2", "property1", "storm")),
    require_prism(rational_function=True)(("brp", "brp_16-2", "property1", "prism")),
    require_stormpy()(("brp", "brp_16-2", "property1", "stormpy")),
]


@pytest.mark.parametrize("name,file,property,tool", benchmarks)
def test_script(name, file, property, tool):
    command = ["--file",
               os.path.join(MODEL_FOLDER, "{}/{}.pm".format(name, file)),
               "--pctl-file",
               os.path.join(MODEL_FOLDER, "{}/{}.pctl".format(name, property)),
               "--{}".format(tool),
               '--result-file',
               target_file
               ]
    compute_solutionfunction.run(command, False)
    assert os.path.isfile(target_file)
    os.remove(target_file)
