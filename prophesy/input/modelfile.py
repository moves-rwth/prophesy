import os
import re
import shutil
import tempfile
import logging

from prophesy.config import configuration
from prophesy.util import ensure_dir_exists, check_filepath_for_reading
from prophesy.data.parameter import ParameterOrder, Parameter
from prophesy.data.model_type import ModelType, model_is_nondeterministic
from prophesy.data import interval
from prophesy.adapter.pycarl import Rational, Variable


logger = logging.getLogger(__name__)


def open_model_file(location):
    _, file_extension = os.path.splitext(location)
    if file_extension == ".drn":
        logger.debug("Assume input is direct encoded")
        return DrnFile(location)
    else:
        logger.debug("Assume input is a Prism File")
        return PrismFile(location)


class DrnFile:
    """
    Wraps a DRN file.
    """

    def __init__(self, location):
        self.location = location
        check_filepath_for_reading(location)
        self.model_type = self._get_model_type()
        self.parameters = ParameterOrder()
        self._get_parameters()

    def contains_nondeterministic_model(self):
        return model_is_nondeterministic(self.model_type)

    def _get_model_type(self):
        with open(self.location) as file:
            for line in file:
                if line.startswith("@type:"):
                    print(line[7:11])
                    if line[7:11] in ["dtmc", "DTMC"]:
                        return ModelType.DTMC
                    elif line[7:10] in ["mdp", "MDP"]:
                        return ModelType.MDP
                    elif line[7:11] in ["ctmc", "CTMC"]:
                        return ModelType.CTMC
                    elif line[7:9] in ["ma", "MA"]:
                            return ModelType.CTMC
                    else:
                        raise NotImplementedError("Support for other types than DTMC and MDPs is not implemented in the parser.")

    def _get_parameters(self):
        with open(self.location) as file:
            logger.debug("Searching for parameters parameters!")
            next_line_has_parameters = False
            for line in file:
                if next_line_has_parameters:
                    parameter_names = line.split()
                    logger.debug("Parameter names: %s", str(parameter_names))
                    for par_name in parameter_names:
                        # TODO change this in order to support variables for rewards.
                        bound = interval.Interval(Rational(0), interval.BoundType.open, Rational(1),
                                                  interval.BoundType.open)
                        self.parameters.append(Parameter(Variable(par_name), bound))
                    return
                if line.startswith("@parameters"):
                    logger.debug("Next line contains parameters!")
                    next_line_has_parameters = True


class PrismFile:
    """
    Wrapper for Prism file; extracts parameter names.
    
    Rationale for not using stormpy bindings: Support for prism file should be given even without stormpy.
    """

    def __init__(self, location):
        assert isinstance(location, str)
        self._is_temp = False
        self.location = location
        check_filepath_for_reading(location)
        self.parameters = ParameterOrder()
        self.model_type = self._model_type()
        self._get_parameters()

    def __del__(self):
        if self._is_temp:
            os.unlink(self.location)
            self._is_temp = False

    def contains_nondeterministic_model(self):
        return model_is_nondeterministic(self.model_type)

    def _model_type(self):
        with open(self.location, 'r') as f:
            for line in f:
                line = line.strip()
                if line.startswith("//"):
                    continue
                if line == "dtmc":
                    return ModelType.DTMC
                if line == "mdp":
                    return ModelType.MDP
                if line == "ctmc":
                    return ModelType.CTMC
                if line == "ma":
                    return ModelType.MA
            raise ValueError("Could not infer model type")

    def _get_parameters(self):
        with open(self.location, 'r') as f:
            inputstring = f.read()
            parameter_names = re.findall("^const double (\w*\s*);", inputstring, re.MULTILINE)
            for par_name in parameter_names:
                #TODO change this in order to support variables for rewards.
                bound = interval.Interval(Rational(0), interval.BoundType.open, Rational(1), interval.BoundType.open)
                self.parameters.append(Parameter(Variable(par_name), bound))

    def make_temporary_copy(self):
        """Makes a temporary copy of itself, which will be deleted automatically.
           Does nothing if a temporary copy already exists."""
        if self._is_temp:
            return
        ensure_dir_exists(configuration.get_intermediate_dir())
        fd, tmpfile = tempfile.mkstemp(suffix=".pm", dir=configuration.get_intermediate_dir(), text=True)
        os.close(fd)
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
