import os
import subprocess
import tempfile

from prophesy.config import configuration
from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.input.samplefile import read_samples_file
from prophesy.util import run_tool, ensure_dir_exists, write_string_to_tmpfile
from prophesy.data.samples import InstantiationResultDict, InstantiationResult
from prophesy.adapter.pycarl import Rational
from prophesy.sampling.sampler import Sampler
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError
import prophesy.data.range


class PrismModelChecker(ParametricProbabilisticModelChecker, Sampler):
    def __init__(self, location=configuration.get_prism()):
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

    def perform_uniform_sampling(self, parameters, samples_per_dimension):
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")
        assert len(self.prismfile.parameters) == len(parameters.get_variables()), "Number of intervals does not match number of parameters"
        assert samples_per_dimension > 1
        ranges = [prophesy.data.range.create_range_from_interval(interval, samples_per_dimension) for interval in parameters.get_variable_bounds()]

        range_strings = ["{0}:{1}:{2}".format(r.start, r.step, r.stop) for r in ranges]
        const_values_string = ",".join(["{0}={1}".format(p, r) for (p, r) in zip(parameters.get_variables(), range_strings)])

        ensure_dir_exists(configuration.get_intermediate_dir())
        _, resultpath = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)
        pctlpath = write_string_to_tmpfile(self.pctlformula)

        args = [self.location, self.prismfile.location, pctlpath,
                "-const", const_values_string,
                "-exportresults", resultpath]
        run_tool(args)
        found_parameters, _, samples = read_samples_file(resultpath, parameters)

        os.unlink(resultpath)
        os.unlink(pctlpath)
        return samples

    def perform_sampling(self, samplepoints):
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")

        ensure_dir_exists(configuration.get_intermediate_dir())
        _, resultpath = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)
        pctlpath = write_string_to_tmpfile(self.pctlformula)

        samples = InstantiationResultDict(self.prismfile.parameters)
        for sample_point in samplepoints:
            const_values_string = ",".join(["{0}={1}".format(var, float(val)) for var, val in sample_point.items()])
            args = [self.location, self.prismfile.location, pctlpath,
                    "-const", const_values_string,
                    "-exportresults", resultpath]
            run_tool(args)
            with open(resultpath) as f:
                f.readline()
                tmp = f.readline()
                assert tmp != None
                assert tmp != ""
                sample_value = Rational(tmp)

            samples.add_result(InstantiationResult(sample_point, sample_value))
        os.unlink(resultpath)
        os.unlink(pctlpath)
        return samples
