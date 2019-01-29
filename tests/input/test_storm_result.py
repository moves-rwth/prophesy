from prophesy.input.solutionfunctionfile import read_pstorm_result

from helpers.helper import get_example_path
from requires import *

@require_pycarl_parser()
def test_read_pstorm_result_brp():
    read_pstorm_result(get_example_path("brp", "brp_16-2.rat"))