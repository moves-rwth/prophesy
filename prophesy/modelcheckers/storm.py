import os
import tempfile
import logging
import re

from prophesy.config import configuration
from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.modelcheckers.pmc import BisimulationType
from prophesy.util import run_tool, ensure_dir_exists
from prophesy.input.solutionfunctionfile import read_pstorm_result
from prophesy.sampling.sampler import Sampler
import prophesy.adapter.pycarl as pc
from prophesy.data.property import Property, OperatorBound
from prophesy.data.samples import InstantiationResultDict, InstantiationResult
from prophesy.data.constant import Constants
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError

logger = logging.getLogger(__name__)


class StormModelChecker(ParametricProbabilisticModelChecker):
    """
    Class wrapping the storm model checker CLI.
    """
    def __init__(self, main_location=configuration.get_storm(), parameter_location=configuration.get_storm_pars()):
        self.main_location = main_location
        self.parameter_location = parameter_location
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
        args = [self.main_location, '--version']
        outputstr = run_tool(args, True)
        output = outputstr.split("\n")
        return output[0]

    def set_bisimulation_type(self, t):
        assert(isinstance(t, BisimulationType))
        self.bisimulation = t

    def set_pctl_formula(self, formula):
        self.pctlformula = formula

    def load_model_from_prismfile(self, prismfile, constants=Constants()):
        self.prismfile = prismfile
        self.constants = constants

    def get_rational_function(self):
        logger.info("Compute solution function")

        if self.pctlformula is None:
            raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile is None:
            raise NotEnoughInformationError("model missing")

        # create a temporary file for the result.
        ensure_dir_exists(configuration.get_intermediate_dir())
        _, resultfile = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)

        constants_string = self.constants.to_key_value_string()

        args = [self.parameter_location,
                '--prism', self.prismfile.location,
                '--prop', str(self.pctlformula),
                '--parametric',
                '--parametric:resultfile', resultfile,
                '--elimination:order', 'fwrev']
        if self.bisimulation == BisimulationType.strong:
            args.append('--bisimulation')
        if constants_string != "":
            args.append('-const')
            args.append(constants_string)

        logger.info("Call storm")
        ret_code = run_tool(args, False)
        if ret_code != 0:
            # TODO throw exception?
            logger.warning("Return code %s after call with %s", ret_code, " ".join(args))
        else:
            logger.info("Storm call finished successfully")

        param_result = read_pstorm_result(resultfile)
        os.remove(resultfile)
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
                    '--prop', str(self.pctlformula),
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
            result = pc.Rational(result)

            samples.add_result(InstantiationResult(sample_point, result))
            os.remove(resultfile)

        return samples

    def check_hyperrectangle(self, parameters, hyperrectangle, threshold, safe):
        logger.info("Check region")

        if self.pctlformula is None:
            raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile is None:
            raise NotEnoughInformationError("model missing")

        region_string = hyperrectangle.to_region_string(parameters.get_variables())
        logger.debug("Region string is {}".format(region_string))
        property_to_check = self.pctlformula
        if safe:
            rel = pc.Relation.GEQ
        else:
            rel = pc.Relation.LESS

        property_to_check.bound = OperatorBound(rel, threshold)
        _, resultfile = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)

        constants_string = self.constants.to_key_value_string(to_float=False) if self.constants else ""

        args = [self.parameter_location,
                '--prism', self.prismfile.location,
                '--prop', str(property_to_check),
                '--region', region_string,
                '--resultfile', resultfile,
                ]
        if self.bisimulation == BisimulationType.strong:
            args.append('--bisimulation')
        if constants_string != "":
            args.append('-const')
            args.append(constants_string)

        logger.info("Call storm")
        ret_code = run_tool(args, False)
        if ret_code != 0:
            logger.warning("Return code %s after call with %s", ret_code, " ".join(args))
            raise RuntimeError("Storm-pars crashed.")
        else:
            logger.info("Storm call finished successfully")

        regions = []
        # with open(resultfile) as f:
        #     for line in f:
        #         res_line = line.split(":")
        #         if len(res_line) != 2:
        #             raise ValueError("Unexpected content in result file")
        #         if res_line[0] == "AllViolated":
        #             region_result = RegionCheckResult.allviolated
        #         elif res_line[0] == "AllSatisfied":
        #             region_result = RegionCheckResult.allsatisfied
        #         elif res_line[0] == "ExistsBoth":
        #             region_result = RegionCheckResult.unknown
        #         elif res_line[0] == "Unknown":
        #             region_result = RegionCheckResult.unknown
        #         else:
        #             raise RuntimeError("Unexpected content in result file")
        #
        #         region_string_out = res_line[1].strip()
        #         region = HyperRectangle.from_region_string(region_string_out)
        #         regions.append(region_result, region)
        return regions



