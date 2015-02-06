#!/usr/bin/python3

import subprocess
import time

SAMPLINGNR = 5
ITERATIONS = 3
current_time = time.strftime("%H_%M", time.localtime())
target_file = "ratfilesampling_{}.out".format(current_time)


benchmarks = [ 
    ("brp/brp_16-2", 0.9, "True"),
#   ("brp/brp_128-2", 0.9, "True"),
#   ("brp/brp_128-5", 0.9, "True"),
#   ("brp/brp_256-2", 0.9, "True"),
#   ("brp/brp_256-5", 0.9, "True"),
    ("crowds/crowds_3-5", 0.9, "True"),
    ("crowds/crowds_5-5", 0.9, "True"),
    ("crowds/crowds_10-5", 0.9, "True"),
    ("crowds/crowds_15-5", 0.9, "True"),
    ("crowds/crowds_20-5", 0.9, "True"),
    ("nand/nand_10-1", 0.5, "True"),
    ("nand/nand_10-2", 0.5, "True"),
    ("nand/nand_10-5", 0.5, "True"),
    ("nand/nand_20-2", 0.5, "True"),
#   ("nand/nand_20-5", 0.5, "True"),
]

def runBenchmarks():
    for (benchmark, threshold, safe_above) in benchmarks:
        command = ["python3",
                    "../ratfilesampling.py", 
                    "--rat-file",
                    "{}.rat".format(benchmark), 
                    "--samples-file",
                    "{}.samples".format(benchmark),
                    "--samplingnr",
                    str(SAMPLINGNR),
                    "--iterations",
                    str(ITERATIONS),
                    "--threshold",
                    str(threshold),
                    "--{}-above-threshold".format("safe" if safe_above else "bad")
                    ]
        output = open(target_file, "a+")
        print("Running ratfilesampling on {} ...".format(benchmark))
        output.write(" ".join(command))
        subprocess.call(command, stdout=output);
        output.write("\n==========================================================\n\n")
        output.close()

    output = open(target_file, "a+")
    output.write("\n==========================================================\n")
    output.write("Run ended.")
    output.close()

runBenchmarks()
