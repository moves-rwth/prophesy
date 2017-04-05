import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import modelsampling

def test_script():
    import time

    EXAMPLE_FOLDER = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "benchmarkfiles/pdtmc")
    SAMPLINGNR = 5
    ITERATIONS = 3
    current_time = time.strftime("%H_%M", time.localtime())

    benchmarks = [
        ("brp", "brp_16_2", "property1", 0.9),
        ("brp", "brp_16_2", "property1", 0.5),
        ("brp", "brp_16_2", "property1", 0.98),
        #   ("brp", "brp_128-2", 0.9, True),
        #   ("brp", "brp_128-5", 0.9, True),
        #   ("brp", "brp_256-2", 0.9, True),
        #   ("brp", "brp_256-5", 0.9, True),
       # ("crowds", "crowds_3-5", 0.9, True),
        #("crowds", "crowds_3-5", 0.5, True),
        #   ("crowds", "crowds_5-5", 0.9, True),
        #   ("crowds", "crowds_10-5", 0.9, True),
        #   ("crowds", "crowds_15-5", 0.9, True),
        #   ("crowds", "crowds_20-5", 0.9, True),
        #("nand", "nand_10-1", 0.1, True),
        #("nand", "nand_10-1", 0.5, True),
        #   ("nand", "nand_10-2", 0.5, True),
        #   ("nand", "nand_10-5", 0.5, True),
        #   ("nand", "nand_20-2", 0.5, True),
        #   ("nand", "nand_20-5", 0.5, True),
        ("nand-reward", "nand_10-2", 0.5, True),
        #   ("nand-reward", "nand_10-5", 0.5, True),
        #   ("nand-reward", "nand_20-2", 0.5, True),
        #   ("nand-reward", "nand_20-5", 0.5, True),
    ]




    for (name, file, property, threshold) in benchmarks:
        command = ["--file",
                   os.path.join(EXAMPLE_FOLDER, "{}/{}.pm".format(name, file)),
                   "--pctl-file",
                   os.path.join(EXAMPLE_FOLDER, "{}/{}.pctl".format(name, property)),
                   "--samplingnr",
                   str(SAMPLINGNR),
                   "--iterations",
                   str(ITERATIONS),
                   "--threshold",
                   str(threshold),
                   "--prism"
                   ]
        modelsampling.run(command, False)