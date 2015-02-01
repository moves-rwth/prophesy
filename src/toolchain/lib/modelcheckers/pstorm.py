import os
import config
import tempfile
import subprocess
from modelcheckers.ppmc import ParametricProbablisticModelChecker,\
    BisimulationType
from util import check_filepath_for_reading, run_tool, ensure_dir_exists
from input.resultfile import read_pstorm_result, ParametricResult
from data.rationalfunction import RationalFunction
from sympy.polys.polytools import Poly
import re
from sympy.core.symbol import Symbol
from sympy.core.numbers import Float

class ProphesyParametricModelChecker(ParametricProbablisticModelChecker):
    def __init__(self, location = config.PARAMETRIC_STORM_COMMAND):
        self.location = location
        self.bisimulation = BisimulationType.none;

    def name(self):
        return "pstorm"

    def version(self):
        args = [self.location, '--version']
        pipe = subprocess.Popen(args, stdout = subprocess.PIPE)
        # pipe.communicate()
        outputstr = pipe.communicate()[0].decode(encoding = 'UTF-8')
        output = outputstr.split("\n")
        return output[len(output) - 2]

    def set_bisimulation_type(self, t):
        assert(isinstance(t, BisimulationType))
        if t == BisimulationType.weak:
            raise RuntimeError("pstorm does not support weak bisimimulation")
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
            raise
        if len(pctl_formulas) > 1:
            print("pctl file contains more than one formula. {0} only takes the first.".format(self.name()))

        # TODO make sure the pctl formula is supported.

        # create a temporary file for the result.
        ensure_dir_exists(config.INTERMEDIATE_FILES_DIR)
        (_, resultfile) = tempfile.mkstemp(suffix = ".txt", dir = config.INTERMEDIATE_FILES_DIR, text = True)

        args = [self.location,
                '--symbolic', prism_file.location,
                '--prop', str(pctl_formulas[0])]
        #,
        #        '--parametric:resultfile', resultfile]
        if self.bisimulation == BisimulationType.strong:
            args.append('--bisimimulation')
        storm_out = run_tool(args, True).decode('UTF-8')
        storm_out = storm_out.split('\n')
        for line in storm_out:
            if line.startswith("Result (initial state): ["):
                ratfunc_str = line.strip()[25:-1]

                parameter_strings = re.findall('[A-Za-z_]\w+', ratfunc_str)
                parameters = set([ name.strip() for name in parameter_strings if name.strip() ])
                parameters = [ Symbol(name) for name in parameters ]
                ratsplit = ratfunc_str.split("/", 1)
                if len(ratsplit) == 2:
                    (ratfunc_nomstr, ratfunc_denstr) = ratsplit
                    nominator = Poly(ratfunc_nomstr, parameters)
                    denominator = Poly(ratfunc_denstr, parameters)
                else:
                    nominator = Poly(ratfunc_str, parameters)
                    denominator = Poly(Float(1), parameters)
                ratfunc = RationalFunction(nominator, denominator)
                return ParametricResult(parameters, [], [], ratfunc)
        else:
            # Error no output
            raise RuntimeError("Storm did not output expected info")
            pass

        paramResult = read_pstorm_result(resultfile)
        os.unlink(resultfile)
        return paramResult
        # /pstorm --symbolic examples/pdtmc/brp/brp_32-4.pm --pctl "P=? [F target]"
