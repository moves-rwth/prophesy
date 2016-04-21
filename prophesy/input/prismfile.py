import os
import re
import shutil
import tempfile
from prophesy import config
from prophesy.util import ensure_dir_exists, check_filepath_for_reading

class PrismFile:
    """Wrapper for Prism file; extracts parameter names."""
    def __init__(self, location):
        assert isinstance(location, str)
        check_filepath_for_reading(location)
        self._is_temp = False
        self.location = location
        self.parameters = []
        self._get_parameters()

    def __del__(self):
        if self._is_temp:
            os.unlink(self.location)

    def _get_parameters(self):
        with open(self.location, 'r') as f:
            inputstring = f.read()
            self.parameters = re.findall("^const double (\w*\s*);", inputstring, re.MULTILINE)

    def make_temporary_copy(self):
        """Makes a temporary copy of itself, which will be deleted automatically.
           Does nothing if a temporary copy already exists."""
        if self._is_temp:
            return
        ensure_dir_exists(config.INTERMEDIATE_FILES)
        _, tmpfile = tempfile.mkstemp(suffix=".pm", dir=config.INTERMEDIATE_FILES, text=True)
        try:
            shutil.copyfile(self.location, tmpfile)
            self.location = tmpfile
            self._is_temp = True
        except:
            os.unlink(tmpfile)
            raise

    def replace_parameter_keyword(self, new_keyword):
        """Substitutes parameter type keywords (e.g. 'const double')
           with the given string (unless the line is commented out)."""
        with open(self.location, 'r') as f:
            inputstring = f.read()
            substitute_regex = "(?<!// )(const double) (\w*\s*;)"
            outputstring, subs = re.subn(substitute_regex, r"{0} \2".format(new_keyword), inputstring, re.MULTILINE)
            if subs != len(self.parameters):
                raise RuntimeError("Number of substitutions does not match number of parameters")
        with open(self.location, 'w') as f:
            f.write(outputstring)

    def nr_parameters(self):
        return len(self.parameters)
