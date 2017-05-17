from prophesy.input.resultfile import read_pstorm_result

from helpers.helper import get_example_path

def test_read_file_1():
    read_pstorm_result(get_example_path("examples", "brp", "brp_16-2.rat"))