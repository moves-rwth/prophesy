import os
from prophesy.config import configuration
import tempfile
import subprocess
from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.modelcheckers.pmc import BisimulationType
from prophesy.util import run_tool, ensure_dir_exists
from prophesy.input.resultfile import read_pstorm_result
from prophesy.sampling.sampler import Sampler
from prophesy.adapter.pycarl import Rational
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError


class StormModelChecker(ParametricProbabilisticModelChecker, Sampler):
    def __init__(self, location=configuration.get_storm()):
        self.location = location
        self.bisimulation = BisimulationType.strong
        self.pctlformula = ""
        self.prismfile = None

    def name(self):
        return "storm"

    def version(self):
        args = [self.location, '--version']
        pipe = subprocess.Popen(args, stdout=subprocess.PIPE)
        # pipe.communicate()
        outputstr = pipe.communicate()[0].decode(encoding='UTF-8')
        output = outputstr.split("\n")
        return output[len(output) - 2]

    def set_bisimulation_type(self, t):
        assert(isinstance(t, BisimulationType))
        self.bisimulation = t


    def set_pctl_formula(self, formula):
        self.pctlformula = formula

    def load_model_from_prismfile(self, prismfile):
        self.prismfile = prismfile

    def get_rational_function(self):
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")

        # create a temporary file for the result.
        ensure_dir_exists(configuration.get_intermediate_dir())
        file, resultfile = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)
        # Delete the file, storm requires that the file does not exist. By this code,
        # we at least get nice and predictable file names.

        args = [self.location,
                '--prism', self.prismfile.location,
                '--prop', self.pctlformula,
                '--parametric',
                '--parametric:resultfile', resultfile]
        if self.bisimulation == BisimulationType.strong:
            args.append('--bisimulation')
        args.append('--elimination:order')
        args.append("fwrev")

        run_tool(args, False)
        param_result = read_pstorm_result(resultfile)
        os.unlink(resultfile)
        return param_result

    def perform_sampling(self, samplepoints):
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")

        # create a temporary file for the result.
        ensure_dir_exists(configuration.get_intermediate_dir())
        _, resultfile = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)

        #raise NotImplementedError("The Storm interface does not support sampling")

        #TODO finish
        samples = {}
        for sample_point in samplepoints:
            const_values_string = ",".join(["{0}={1}".format(var, val) for var, val in sample_point.items()])
            args = [self.location,
                    '--prism', self.prismfile.location,
                    '--prop', self.pctlformula,
                    "-const", const_values_string]
            if self.bisimulation == BisimulationType.strong:
                args.append('--bisimulation')

            output = run_tool(args, quiet=True)
            with open(resultfile) as f:
                f.readline()
                sample_value = Rational(f.readline())

            pt = sample_point.get_point(self.prismfile.parameters)
            samples[pt] = sample_value

        os.unlink(resultfile)
        return samples
