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

    def load_model_from_prismfile(self, path):
        self.prismfile = PrismFile(path)

    def get_rational_function(self):
        # create a temporary file for the result.
        ensure_dir_exists(config.INTERMEDIATE_FILES_DIR)
        _, resultfile = tempfile.mkstemp(suffix=".txt", dir=config.INTERMEDIATE_FILES_DIR, text=True)

        args = [self.location,
                '--symbolic', self.prismfile.location,
                '--prop', self.pctlformula),
                '--parametric:resultfile', resultfile]
        if self.bisimulation == BisimulationType.strong:
            args.append('--bisimulation')
        args.append('--sparseelim:order')
        args.append("fwrev")

        run_tool(args, False)
        param_result = read_pstorm_result(resultfile)
        os.unlink(resultfile)
        return param_result

    def sample(self, samplepoints):

        raise NotImplementedError("The Storm interface does not support sampling")
        check_filepath_for_reading(pctl_filepath)

        # get the pctl string from the file.
        pctl_formulas = self._parse_pctl_file(pctl_filepath)
        if len(pctl_formulas) == 0:
            raise
        if len(pctl_formulas) > 1:
            print("pctl file contains more than one formula. {0} only takes the first.".format(self.name()))



