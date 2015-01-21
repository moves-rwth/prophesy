import re
import config
import tempfile
import shutil
import os

class PrismFile():
    def __init__(self, location):
        self.location = location
        self.parameters = self._get_parameters()
        self.is_temp = False

    def __del__(self):
        if self.is_temp:
            os.unlink(self.location)

    def _get_parameters(self):
        with open(self.location, 'r') as f:
            inputstring = f.read()
            self.parameters = re.findall("^const double (\w*\s*);", inputstring, re.MULTILINE)

    def make_temporary_copy(self):
        """Makes a temporary copy of itself, which get deleted automatically.
        Does nothing if already a temporary copy"""
        if self.is_temp:
            return
        self.is_temp = True
        tmpfile = tempfile.mkstemp(suffix = ".pm", dir = config.CLI_INTERMEDIATE_FILES_DIR, text = True)
        try:
            shutil.copyfile(self.location, tmpfile[1])
            self.location = tmpfile[1]
            self.is_temp = True
        except:
            os.unlink(tmpfile[1])
            raise

    def replace_parameter_keyword(self, new_keyword):
        with open(self.location, 'r') as f:
            inputstring = f.read()
            (outputstring, subs) = re.subn("(?<!// )(const double) (\w*\s*;)", r"{0} \2".format(new_keyword), inputstring, re.MULTILINE)
            if subs != len(self.parameters):
                raise RuntimeError("Number of substitutions does not match number of parameters")
        with open(self.location, 'w') as f:
            f.write(outputstring)

    def nr_parameters(self):
        return len(self.parameters)
