import os
import subprocess
import tempfile

import config
from input.resultfile import read_pstorm_result
from modelcheckers.ppmc import ParametricProbabilisticModelChecker, \
    BisimulationType
from util import check_filepath_for_reading, run_tool, ensure_dir_exists


class ProphesyParametricModelChecker(ParametricProbabilisticModelChecker):
    def __init__(self, location=config.PARAMETRIC_STORM_COMMAND):
        self.location = location
        self.bisimulation = BisimulationType.strong

    def name(self):
        return "pstorm"

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
            raise RuntimeError("No PCTL formula specified")
        if len(pctl_formulas) > 1:
            print("pctl file contains more than one formula. {0} only takes the first.".format(self.name()))

        # TODO make sure the pctl formula is supported.

        # create a temporary file for the result.
        ensure_dir_exists(config.INTERMEDIATE_FILES_DIR)
        _, resultfile = tempfile.mkstemp(suffix=".txt", dir=config.INTERMEDIATE_FILES_DIR, text=True)

        args = [self.location,
                '--symbolic', prism_file.location,
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
