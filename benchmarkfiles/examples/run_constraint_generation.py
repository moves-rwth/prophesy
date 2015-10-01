#!/usr/bin/python3

import subprocess
import time

THRESHOLD_AREA = 0.001
END_CRITERIA = "--area"
END_CRITERIA_VALUE = 0.95
current_time = time.strftime("%H_%M", time.localtime())
target_file = "constraint_generation_{}".format(current_time)


benchmarks = [ 
    ("brp/", "brp_16-2"),
    ("crowds/", "crowds_3-5"),
    ("nand/", "nand_10-1"),
    ("crowds/", "crowds_5-5"),
    ("crowds/", "crowds_10-5"),
    ("nand/", "nand_10-2"),
    ("nand-reward/", "nand_10-2"),
    ("crowds/", "crowds_15-5"),
    ("nand/", "nand_10-5"),
    ("nand-reward/", "nand_10-5"),
    ("crowds/", "crowds_20-5"),
    ("nand/", "nand_20-2"),
    ("nand-reward/", "nand_20-2"),
#   ("nand/", "nand_20-5"),
#   ("nand-reward/", "nand_20-5"),
#   ("brp/", "brp_128-2"),
#   ("brp/", "brp_128-5"),
#   ("brp/", "brp_256-2"),
#   ("brp/", "brp_256-5"),
]

def runBenchmarks():
    for (name, benchmark) in benchmarks:
        for algorithm in ["rectangles", "quads"]:
            file_output = "{}_{}_{}.out".format(target_file, benchmark, algorithm)
            command = ["python3",
                        "../buildconstraints.py", 
                        "--rat-file",
                        "{}{}.rat".format(name, benchmark),
                        "--samples-file",
                        "{}{}.samples".format(name, benchmark),
                        "--z3",
                        "z3",
                        END_CRITERIA,
                        str(END_CRITERIA_VALUE),
                        "--{}".format(algorithm),
                        ]
            output = open(file_output, "a+")
            print("Running buildconstraints on {} ...".format(benchmark))
            output.write(" ".join(command))
            subprocess.call(command, stdout=output);
            output.write("\n==========================================================\n\n")
            output.close()

runBenchmarks()