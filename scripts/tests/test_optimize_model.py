import os
import random

from click.testing import CliRunner
import pytest
import numpy as np

from conftest import EXAMPLE_FOLDER
from requires import require_stormpy

from optimize_model import model_optimization


# TODO: extract to helper module
def set_random_seeds(py_seed=42, np_seed=23):
    random.seed(py_seed)
    np.random.seed(np_seed)


TEST_CASES = [
    require_stormpy()(('crowds', 'crowds_3-5.pm', 'P=? [F "observe0Greater1"]', 'min', (42, 23), '0.066204196290612569')),
    require_stormpy()(('brp', 'brp_16-2.pm', 'P=? [F "target"]', 'max', (42, 23), '0.31868193758344365')),
]


@pytest.mark.parametrize('folder, file, pctl_property, direction, random_seeds, some_parameter_val', TEST_CASES)
def test_optimize_model(folder, file, pctl_property, direction, random_seeds, some_parameter_val):
    set_random_seeds(*random_seeds)
    result = CliRunner().invoke(model_optimization, ['--prism-file', os.path.join(EXAMPLE_FOLDER, folder, file),
                                                     '--pctl-string', pctl_property,
                                                     '--direction', direction])

    print(result.output)
    assert not result.exception
    assert some_parameter_val in result.output
