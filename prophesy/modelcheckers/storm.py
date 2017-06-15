import os
from prophesy.config import configuration
import tempfile
import subprocess
import logging
import re

from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.modelcheckers.pmc import BisimulationType
from prophesy.util import run_tool, ensure_dir_exists
from prophesy.input.resultfile import read_pstorm_result
from prophesy.sampling.sampler import Sampler
from prophesy.adapter.pycarl import Rational
from prophesy.data.samples import InstantiationResultDict, InstantiationResult,  ParameterInstantiation
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError

logger = logging.getLogger(__name__)


class StormModelChecker(ParametricProbabilisticModelChecker, Sampler):
    """
    Class wrapping the storm model checker CLI.
    """
    def __init__(self, location=configuration.get_storm()):
        self.location = location
        self.bisimulation = BisimulationType.strong
        self.pctlformula = ""
        self.prismfile = None
        self.constants = None

    def name(self):
        """
        :return: The name of the model sample engine
        """
        return "storm"

    def version(self):
        """
        
        :return: Version information about the model checker
        """
        args = [self.location, '--version']
        pipe = subprocess.Popen(args, stdout=subprocess.PIPE)
        # pipe.communicate()
        outputstr = pipe.communicate()[0].decode(encoding='UTF-8')
        output = outputstr.split("\n")
        return output[0]

    def set_bisimulation_type(self, t):
        assert(isinstance(t, BisimulationType))
        self.bisimulation = t


    def set_pctl_formula(self, formula):
        self.pctlformula = formula

    def load_model_from_prismfile(self, prismfile, constants=None):
        self.prismfile = prismfile
        self.constants = constants

    def get_rational_function(self):
        logger.info("Compute solution function")

        if self.pctlformula is None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile is None: raise NotEnoughInformationError("model missing")

        # create a temporary file for the result.
        ensure_dir_exists(configuration.get_intermediate_dir())
        file, resultfile = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)

        constants_string = self.constants.to_key_value_string()

        args = [self.location,
                '--prism', self.prismfile.location,
                '--prop', self.pctlformula,
                '--parametric',
                '--parametric:resultfile', resultfile]
        if self.bisimulation == BisimulationType.strong:
            args.append('--bisimulation')
        if constants_string != "":
            args.append('-const')
            args.append(constants_string)
        args.append('--elimination:order')
        args.append("fwrev")

        logger.info("Call storm")
        ret_code = run_tool(args, False)
        if ret_code != 0:
            logger.warning("Return code %s after call with %s", ret_code, " ".join(args))
        else:
            logger.info("Storm call finished successfully")

        param_result = read_pstorm_result(resultfile)
        os.unlink(resultfile)
        return param_result

    def perform_sampling(self, samplepoints, constants=None):
        logger.info("Perform uniform sampling")
        if self.pctlformula == None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile == None: raise NotEnoughInformationError("model missing")

        # create a temporary file for the result.
        ensure_dir_exists(configuration.get_intermediate_dir())

        samples = InstantiationResultDict(samplepoints.parameters)
        for sample_point in samplepoints:
            _, resultfile = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)

            const_values_string = ",".join(["{0}={1}".format(parameter.variable, val) for parameter, val in sample_point.items()])
            constants_string = self.constants.to_key_value_string(to_float=True)
            if constants_string != "":
                const_values_string = const_values_string + "," + constants_string

            args = [self.location,
                    '--prism', self.prismfile.location,
                    '--prop', self.pctlformula,
                    "-const", const_values_string]
            if self.bisimulation == BisimulationType.strong:
                args.append('--bisimulation')

            logger.info("Call storm")
            ret_code = run_tool(args, quiet=False, logfile=resultfile)
            if ret_code != 0:
                logger.warning("Return code %s after call with %s", ret_code, " ".join(args))
            else:
                logger.info("Storm call finished successfully")
                logger.debug("Storm output logged in %s", resultfile)

            result = None
            with open(resultfile) as f:
                for line in f:
                    match = re.search(r"Result (.*): (.*)", line)
                    if match:
                        # Check for exact result
                        match_exact = re.search(r"(.*) \(approx. .*\)", match.group(2))
                        if match_exact:
                            result = match_exact.group(1)
                            break
                        else:
                            result = match.group(2)
                            break
            if result is None:
                raise RuntimeError("Could not find result from storm in {}".format(resultfile))
            result = Rational(result)

            samples.add_result(InstantiationResult(sample_point, result))
            os.unlink(resultfile)

        return samples
