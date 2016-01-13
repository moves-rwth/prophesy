import os
from config import configuration
import config
import tempfile
import subprocess
from modelcheckers.ppmc import ParametricProbabilisticModelChecker
from modelcheckers.pmc import BisimulationType
from util import check_filepath_for_reading, run_tool, ensure_dir_exists
from input.resultfile import read_pstorm_result
from input.prismfile import PrismFile


class StormModelChecker(ParametricProbabilisticModelChecker):
    def __init__(self, location=configuration.get(config.EXTERNAL_TOOLS, "storm")):
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
        ensure_dir_exists(config.INTERMEDIATE_FILES)
        _, resultfile = tempfile.mkstemp(suffix=".txt", dir=config.INTERMEDIATE_FILES, text=True)

        args = [self.location,
                '--symbolic', self.prismfile.location,
                '--prop', self.pctlformula,
                '--parametric',
                '--parametric:resultfile', resultfile]
        if self.bisimulation == BisimulationType.strong:
            args.append('--bisimulation')
        args.append('--sparseelim:order')
        args.append("fwrev")

        run_tool(args, False)
        param_result = read_pstorm_result(resultfile)
        os.unlink(resultfile)
        return param_result

    def uniform_sample(self, ranges):
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")


        raise NotImplementedError("The Storm interface does not support sampling")


    def sample(self, samplepoints):
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")

        # create a temporary file for the result.
        ensure_dir_exists(config.INTERMEDIATE_FILES)
        _, resultfile = tempfile.mkstemp(suffix=".txt", dir=config.INTERMEDIATE_FILES, text=True)


        raise NotImplementedError("The Storm interface does not support sampling")


        samples = {}
        for pt in samplepoints:
            const_values_string = ",".join(["{0}={1}".format(p, v) for (p, v) in zip(self.prismfile.parameters, pt)])
            args = [self.location,
                    '--symbolic', self.prismfile.location,
                    '--prop', self.pctlformula,
                    "-const", const_values_string,
                    "--exportresults", resultfile]
            if self.bisimulation == BisimulationType.strong:
                args.append('--bisimulation')

            run_tool(args)
            with open(resultfile) as f:
                f.readline()
                sample_value = float(f.readline())
            samples[pt] = sample_value
        os.unlink(resultpath)

