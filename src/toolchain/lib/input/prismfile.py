import re
from util import *
import config
import tempfile
import shutil

def findParametersInPrismFile(path, replace_keyword=None):
        with open(path, 'r') as f:
            inputstring = f.read()
        parameters = re.findall("^const double (\w*\s*);", inputstring, re.MULTILINE)
        if replace_keyword != None:
            (outputstring, subs) = re.subn("(?<!// )(const double) (\w*\s*;)", r"{0} \2".format(replace_keyword), inputstring, re.MULTILINE)
            if subs != len(parameters): 
                raise RuntimeError("Number of substitutions does not match number of parameters")
            with open(path, 'w') as f:
                f.write(outputstring)
        return parameters
            

class PrismFile():
    def __init__(self, location):
        self.location = location
        self.parameters = findParametersInPrismFile(location)
        
    def make_temporary_copy(self):
        ensure_dir_exists(config.CLI_INTERMEDIATE_FILES_DIR)
        tmpfile = tempfile.mkstemp(suffix=".pm",dir=config.CLI_INTERMEDIATE_FILES_DIR, text=True)
        shutil.copyfile(self.location, tmpfile[1])
        return PrismFile(tmpfile[1])
    
    def replace_parameter_keyword(self, new_keyword):
        findParametersInPrismFile(self.location, new_keyword)
        
    def nr_parameters(self):
        return len(self.parameters)
        
        


         