import os
from config import *

"""

"""
def samplepoints_to_file(name, parameters, threshold, results_value):
    path = os.path.join(INTERMEDIATE_FILES, SAMPLES_SUBDIR)
    if not os.path.exists(path):
        os.makedirs(path)
    f = open(os.path.join(path, name) + '.samples', 'w')
    f.write('## INFO:\n')
    f.write('## name: ' + name + '\n')
    f.write('## PARAMETERS:\n')
    f.write(" ".join(map(str,list(parameters))) + '\n')
    f.write('## THRESHOLD:\n')
    f.write(str(threshold) + '\n')
    f.write('## SAMPLES:\n')
    for coordinates, value in results_value.items():
        f.write(" ".join(map(str,list(coordinates))) + ' ' + str(value) + '\n')
    f.close()
    return os.path.join(path, name) + '.samples'
        
       
   