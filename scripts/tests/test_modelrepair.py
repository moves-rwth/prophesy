import os

from click.testing import CliRunner
import pytest

from conftest import EXAMPLE_FOLDER
from requires import require_stormpy
from util import set_random_seeds

from modelrepair import model_repair


# these all do the essentially the same thing; just keeping this here for reference
REDUNDANT_TEST_CASES = [
    require_stormpy()(('brp', 'brp_16-2.pm', 'P<=0.95 [F "target"]', '(+ (* (- pK 0.6) (- pK 0.6)) (* (- pL 0.7) (- pL 0.7)))', (42, 23), '0.0007276219992536925')),
    require_stormpy()(('brp', 'brp_16-2.pm', 'P<=0.95 [F "target"]', '(+ (* (- pK 0.6) (- pK 0.6)) (* (- pL 0.7) (- pL 0.7)))', (51, 17), '0.0007289027210649927')),
    require_stormpy()(('brp', 'brp_16-2.pm', 'P<=0.98 [F "target"]', '(+ (* (- pK 0.3) (- pK 0.3)) (* (- pL 0.8) (- pL 0.8)))', (42, 23), '0.03000731276499133')),
    require_stormpy()(('brp', 'brp_16-2.pm', 'P<=0.999 [F "target"]', '(+ (* (- pK 0.0) (- pK 0.0)) (* (- pL 0.0) (- pL 0.0)))', (42, 23), '0.5903080962075024')),
]
# we're living busy lives, so let's just use the first one
TEST_CASES = REDUNDANT_TEST_CASES[:1]


@pytest.mark.parametrize('folder, file, pctl_property, cost_function, random_seeds, expected_score', TEST_CASES)
def test_modelrepair(folder, file, pctl_property, cost_function, random_seeds, expected_score):
    set_random_seeds(*random_seeds)
    result = CliRunner().invoke(model_repair, ['--prism-file', os.path.join(EXAMPLE_FOLDER, folder, file),
                                               '--pctl-string', pctl_property,
                                               '--cost-function', cost_function])

    assert not result.exception
    assert "score " + expected_score[:10] in result.output
