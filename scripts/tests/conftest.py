import sys
import os
import time
import prophesy.config
import logging

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
logging.basicConfig(filename="prophesy_script_test.log", format='%(levelname)s:%(message)s', level=logging.DEBUG)
EXAMPLE_FOLDER = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                              "benchmarkfiles")

current_time = time.strftime("%H_%M", time.localtime())
prophesy.config.load_configuration()