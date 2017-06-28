import sys
import os
import time

import pytest

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import ratfilesampling


EXAMPLE_FOLDER = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "benchmarkfiles/examples")
SAMPLINGNR = 4
ITERATIONS = 2
current_time = time.strftime("%H_%M", time.localtime())
target_file = "ratfilesampling_{}".format(current_time)

benchmarks = [
    ("brp", "brp_16-2", 0.9, False),
 #   ("brp", "brp_16-2", 0.5, True),
#    ("brp", "brp_16-2", 0.98, True),
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
  #  ("nand-reward", "nand_10-2", 0.5, True),
    #   ("nand-reward", "nand_10-5", 0.5, True),
    #   ("nand-reward", "nand_20-2", 0.5, True),
    #   ("nand-reward", "nand_20-5", 0.5, True),
]

@pytest.mark.parametrize("name,benchmark,threshold,safe_above", benchmarks)
def test_script(name, benchmark, threshold, safe_above):

    command = ["--rat-file",
               os.path.join(EXAMPLE_FOLDER, "{}/{}.rat".format(name, benchmark)),
               "--samples-file",
               os.path.join(EXAMPLE_FOLDER, "{}/{}.samples".format(name, benchmark)),
               "--samplingnr",
               str(SAMPLINGNR),
               "--iterations",
               str(ITERATIONS),
               "--threshold",
               str(threshold),
               ]
    if not safe_above:
        command.append("--bad-above-threshold")
    ratfilesampling.run(command, False)