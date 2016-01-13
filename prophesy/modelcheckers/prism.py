import os
import subprocess
import tempfile
from collections import OrderedDict

from config import configuration
import config
from modelcheckers.ppmc import ParametricProbabilisticModelChecker
from sampling.sampling import read_samples_file
from input.prismfile import PrismFile
from util import check_filepath_for_reading, run_tool, ensure_dir_exists, write_string_to_tmpfile


class PrismModelChecker(ParametricProbabilisticModelChecker):
    def __init__(self, location=configuration.get(config.EXTERNAL_TOOLS, "prism")):
        self.location = location
        self.pctlformula = None
        self.prismfile = None

    def set_pctl_formula(self, formula):
        self.pctlformula = formula

    def load_model_from_prismfile(self, prismfile):
        self.prismfile = prismfile

    def name(self):
        return "prism"

    def version(self):
        args = [self.location, '-version']
        pipe = subprocess.Popen(args, stdout=subprocess.PIPE)
        # pipe.communicate()
        return pipe.communicate()[0].decode(encoding='UTF-8')

    def get_rational_function(self):
        raise NotImplementedError("This is missing")

    def uniform_sample(self, ranges):
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")
        assert len(self.prismfile.parameters) == len(ranges), "Number of value ranges does not match number of parameters"

        range_strings = ["{0}:{1}:{2}".format(r.start, r.step, r.stop) for r in ranges]
        const_values_string = ",".join(["{0}={1}".format(p, r) for (p, r) in zip(self.prismfile.parameters, range_strings)])

        ensure_dir_exists(config.INTERMEDIATE_FILES)
        _, resultpath = tempfile.mkstemp(suffix=".txt", dir=config.INTERMEDIATE_FILES, text=True)
        pctlpath = write_string_to_tmpfile(self.pctlformula)



        args = [self.location, self.prismfile.location, pctlpath,
                "-const", const_values_string,
                "-exportresults", resultpath]
        run_tool(args)
        found_parameters, samples = read_samples_file(resultpath)
        os.unlink(resultpath)
        os.unlink(pctlpath)
        if found_parameters != self.prismfile.parameters:
            raise RuntimeError("Prism returns parameters different from the parameters in the prism file")
        return samples

    def sample(self,samplepoints):
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")


        ensure_dir_exists(config.INTERMEDIATE_FILES)
        _, resultpath = tempfile.mkstemp(suffix=".txt", dir=config.INTERMEDIATE_FILES, text=True)
        pctlpath = write_string_to_tmpfile(self.pctlformula)

        samples = {}
        for pt in samplepoints:
            const_values_string = ",".join(["{0}={1}".format(p, v) for (p, v) in zip(self.prismfile.parameters, pt)])
            args = [self.location, self.prismfile.location, pctlpath,
                    "-const", const_values_string,
                    "-exportresults", resultpath]
            run_tool(args)
            with open(resultpath) as f:
                f.readline()
                sample_value = float(f.readline())
            samples[pt] = sample_value
        os.unlink(resultpath)
        os.unlink(pctlpath)
        return OrderedDict(sorted(samples))
