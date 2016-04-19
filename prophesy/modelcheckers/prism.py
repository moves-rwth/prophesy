import os
import subprocess
import tempfile

from prophesy.config import configuration
from prophesy import config
from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.input.samplefile import read_samples_file
from prophesy.util import run_tool, ensure_dir_exists, write_string_to_tmpfile
from prophesy.data.samples import SampleDict
from pycarl import Rational
from prophesy.sampling.sampler import Sampler
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError

class PrismModelChecker(ParametricProbabilisticModelChecker, Sampler):
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

    def perform_uniform_sampling(self, variables, intervals, samples_per_dimension):
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")
        assert len(self.prismfile.parameters) == len(intervals), "Number of intervals does not match number of parameters"
        assert samples_per_dimension > 1
        assert False, "Need to map given variable order to prismfile variable order"
        ranges = [range.create_range_from_interval(interval, samples_per_dimension) for interval in intervals]

        range_strings = ["{0}:{1}:{2}".format(r.start, r.step, r.stop) for r in ranges]
        const_values_string = ",".join(["{0}={1}".format(p, r) for (p, r) in zip(self.prismfile.parameters, range_strings)])

        ensure_dir_exists(config.INTERMEDIATE_FILES)
        _, resultpath = tempfile.mkstemp(suffix=".txt", dir=config.INTERMEDIATE_FILES, text=True)
        pctlpath = write_string_to_tmpfile(self.pctlformula)

        args = [self.location, self.prismfile.location, pctlpath,
                "-const", const_values_string,
                "-exportresults", resultpath]
        run_tool(args)
        found_parameters, _, samples = read_samples_file(resultpath)
        assert False, "compare found_parameters with variables, reorder as needed"
        os.unlink(resultpath)
        os.unlink(pctlpath)
        if found_parameters != self.prismfile.parameters:
            raise RuntimeError("Prism returns parameters different from the parameters in the prism file")
        return samples

    def perform_sampling(self, samplepoints):
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")

        ensure_dir_exists(config.INTERMEDIATE_FILES)
        _, resultpath = tempfile.mkstemp(suffix=".txt", dir=config.INTERMEDIATE_FILES, text=True)
        pctlpath = write_string_to_tmpfile(self.pctlformula)

        samples = SampleDict(self.prismfile.parameters)
        for sample_point in samplepoints:
            const_values_string = ",".join(["{0}={1}".format(var, val) for var, val in sample_point.items()])
            args = [self.location, self.prismfile.location, pctlpath,
                    "-const", const_values_string,
                    "-exportresults", resultpath]
            run_tool(args)
            with open(resultpath) as f:
                f.readline()
                sample_value = Rational(f.readline())

            pt = sample_point.get_point(self.prismfile.parameters)
            samples[pt] = sample_value
        os.unlink(resultpath)
        os.unlink(pctlpath)
        return samples
