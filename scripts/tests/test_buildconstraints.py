
import subprocess
import time

import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import buildconstraints

def test_script():
    THRESHOLD_AREA = 0.001
    END_CRITERIA = "--area"
    END_CRITERIA_VALUE = 0.30
    current_time = time.strftime("%H_%M", time.localtime())
    target_file = "constraint_generation_{}".format(current_time)

    EXAMPLE_FOLDER = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                                  "benchmarkfiles/examples")

    benchmarks = [
        ("brp/", "brp_16-2", 0.95),
       # ("crowds/", "crowds_3-5", 0.5),
        ("nand/", "nand_10-1", 0.3),
        #("crowds/", "crowds_5-5", 0.5),
        #("crowds/", "crowds_10-5", 0.5),
        #("nand/", "nand_10-2", 0.8),
        #("nand-reward/", "nand_10-1", 0.8),
        #("crowds/", "crowds_15-5", 0.5),
        #("nand/", "nand_10-5", 0.7),
        #("nand-reward/", "nand_10-5", 0.7),
        #("crowds/", "crowds_20-5", 0.6),
        #("nand/", "nand_20-2", 0.3),
        #("nand-reward/", "nand_20-2", 0.4),
    #   ("nand/", "nand_20-5"),
    #   ("nand-reward/", "nand_20-5"),
    #   ("brp/", "brp_128-2"),
    #   ("brp/", "brp_128-5"),
    #   ("brp/", "brp_256-2"),
    #   ("brp/", "brp_256-5"),
    ]

    for (name, benchmark, threshold) in benchmarks:
        for algorithm in ["rectangles", "quads"]:
            command = [
                        "--rat-file",
                        os.path.join(EXAMPLE_FOLDER, "{}{}.rat".format(name, benchmark)),
                        "--samples-file",
                        os.path.join(EXAMPLE_FOLDER, "{}{}.samples".format(name, benchmark)),
                        "--z3",
                        "--threshold",
                        str(threshold),
                        END_CRITERIA,
                        str(END_CRITERIA_VALUE),
                        "--{}".format(algorithm),
                        ]
            buildconstraints.run(command, False)
