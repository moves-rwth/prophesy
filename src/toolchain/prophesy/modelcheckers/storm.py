import os
from config import configuration
import config
import tempfile
import subprocess
from modelcheckers.ppmc import ParametricProbabilisticModelChecker, \
    BisimulationType
from modelcheckers.pmc import ProbabilisticModelChecker
from util import check_filepath_for_reading, run_tool, ensure_dir_exists
from input.resultfile import read_pstorm_result


class StormModelChecker(ParametricProbabilisticModelChecker, ProbabilisticModelChecker):
    def __init__(self, location=configuration.get(config.EXTERNAL_TOOLS, "storm")):
        self.location = location
        self.bisimulation = BisimulationType.strong

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
        if t == BisimulationType.weak:
            raise RuntimeError("pstorm does not support weak bisimulation")
        self.bisimulation = t

    def _parse_pctl_file(self, path):
        with open(path, 'r') as f:
            # TODO use pctl_formula object
            return [line.strip() for line in f if line.strip()[0] != '#']

    def get_rational_function(self, prism_file, pctl_filepath):
        check_filepath_for_reading(pctl_filepath, "pctl file")

        # get the pctl string from the file.
        pctl_formulas = self._parse_pctl_file(pctl_filepath)
        if len(pctl_formulas) == 0:
            raise RuntimeError("No PCTL formula in file / Parse error")
        if len(pctl_formulas) > 1:
            print("pctl file contains more than one formula. {0} only takes the first.".format(self.name()))

        # TODO make sure the pctl formula is supported.

        # create a temporary file for the result.
        ensure_dir_exists(config.INTERMEDIATE_FILES)
        _, resultfile = tempfile.mkstemp(suffix=".txt", dir=config.INTERMEDIATE_FILES, text=True)

        args = [self.location,
                '--symbolic', prism_file.location,
                '--parametric',
                '--prop', str(pctl_formulas[0]),
                '--parametric:resultfile', resultfile]
        if self.bisimulation == BisimulationType.strong:
            args.append('--bisimulation')
            args.append('--sparseelim:order')
            args.append("fwrev")
            pass
        run_tool(args, False) #.decode('UTF-8')

        param_result = read_pstorm_result(resultfile)
        os.unlink(resultfile)
        return param_result

    def sample_pctl_formula(self, prism_filepath, pctl_filepath, samplepoints):
        check_filepath_for_reading(pctl_filepath)

        # get the pctl string from the file.
        pctl_formulas = self._parse_pctl_file(pctl_filepath)
        if len(pctl_formulas) == 0:
            raise
        if len(pctl_formulas) > 1:
            print("pctl file contains more than one formula. {0} only takes the first.".format(self.name()))

    def uniform_sample_pctl_formula(self, prism_file, pctl_file, ranges):
        raise NotImplementedError
