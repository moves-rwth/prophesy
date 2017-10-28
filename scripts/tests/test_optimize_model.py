import os

from click.testing import CliRunner
import pytest

from conftest import EXAMPLE_FOLDER
from requires import require_stormpy
from util import set_random_seeds

from optimize_model import model_optimization


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

    assert not result.exception
    assert some_parameter_val in result.output
