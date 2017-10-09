import os
import tempfile
import logging
import re

from prophesy.config import configuration
from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.modelcheckers.pmc import BisimulationType
from prophesy.regions.region_checker import RegionCheckResult
from prophesy.util import run_tool, ensure_dir_exists
from prophesy.input.solutionfunctionfile import read_pstorm_result
import prophesy.adapter.pycarl as pc
from prophesy.data.property import Property, OperatorBound
from prophesy.data.samples import InstantiationResultDict, InstantiationResult, InstantiationResultFlag
from prophesy.data.constant import Constants
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError

logger = logging.getLogger(__name__)


class StormModelChecker(ParametricProbabilisticModelChecker):
    """
    Class wrapping the storm model checker CLI.
    """

    def __init__(self, main_location=configuration.get_storm(), parameter_location=configuration.get_storm_pars()):
        """
        Constructor.
        :param main_location: Path to main storm binary.
        :param parameter_location: Path to storm-pars binary.
        """
        self.main_location = main_location
        self.parameter_location = parameter_location
        self.bisimulation = BisimulationType.strong
        self.pctlformula = ""
        self.prismfile = None
        self.constants = None

    def name(self):
        return "storm"

    def version(self):
        args = [self.main_location, '--version']
        outputstr = run_tool(args, True)
        output = outputstr.split("\n")
        output = output[0].split(maxsplit=1)
        return output[1]

    def set_bisimulation_type(self, t):
        assert (isinstance(t, BisimulationType))
        self.bisimulation = t

    def set_pctl_formula(self, formula):
        self.pctlformula = formula

    def load_model_from_prismfile(self, prismfile, constants=Constants()):
        self.prismfile = prismfile
        self.constants = constants

    def get_parameter_constraints(self):
        if self.prismfile is None:
            raise NotEnoughInformationError("model missing")
        if self.pctlformula is None:
            raise NotEnoughInformationError("pctl formula missing")  # TODO not strictly necessary

        ensure_dir_exists(configuration.get_intermediate_dir())
        _, resultfile = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)

        constants_string = self.constants.to_key_value_string(to_float=False) if self.constants else ""

        args = [self.parameter_location,
                '--prism', self.prismfile.location,
                '--prop', str(self.pctlformula),
                '--parametric',
                '--parametric:resultfile', resultfile,
                '--onlyconstraints']
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

        param_result = read_pstorm_result(resultfile, False)
        return param_result.welldefined_constraints, param_result.graph_preservation_constraints

    def get_rational_function(self):
        logger.info("Compute solution function")

        if self.pctlformula is None:
            raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile is None:
            raise NotEnoughInformationError("model missing")

        # create a temporary file for the result.
        ensure_dir_exists(configuration.get_intermediate_dir())
        _, resultfile = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)

        constants_string = self.constants.to_key_value_string(to_float=False) if self.constants else ""

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

    def perform_sampling(self, samplepoints):
        logger.info("Perform batch sampling")
        if self.pctlformula is None:
            raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile is None:
            raise NotEnoughInformationError("model missing")

        # create a temporary file for the result.
        ensure_dir_exists(configuration.get_intermediate_dir())

        samples = InstantiationResultDict(samplepoints.parameters)
        for sample_point in samplepoints:
            _, resultfile = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)

            const_values_string = ",".join(
                ["{0}={1}".format(parameter.variable, val) for parameter, val in sample_point.items()])
            constants_string = self.constants.to_key_value_string(to_float=False) if self.constants else ""
            if constants_string != "":
                const_values_string = const_values_string + "," + constants_string

            args = [self.main_location,
                    '--prism', self.prismfile.location,
                    '--prop', str(self.pctlformula),
                    "-const", const_values_string]
            if self.bisimulation == BisimulationType.strong:
                args.append('--bisimulation')

            logger.info("Call storm")
            ret_code = run_tool(args, quiet=False, outputfile=resultfile)
            if ret_code != 0:
                logger.debug("Storm output logged in %s", resultfile)
                # Do not crash here
            else:
                logger.info("Storm call finished successfully")
                logger.debug("Storm output logged in %s", resultfile)

            result = None
            with open(resultfile) as f:
                for line in f:
                    if "Substitution yielding negative" in line:
                        result = InstantiationResultFlag.NOT_WELLDEFINED
                        ret_code = 0
                        break
                    match = re.search(r"Result (.*): (.*)", line)
                    if match:
                        # Check for exact result
                        match_exact = re.search(r"(.*) \(approx. .*\)", match.group(2))
                        if match_exact:
                            result = pc.Rational(match_exact.group(1))
                            break
                        else:
                            result = pc.Rational(match.group(2))
                            break
            if result is None:
                raise RuntimeError("Could not find result from storm in {}".format(resultfile))
            if ret_code != 0:
                raise RuntimeError("Storm crashed.")

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
        property_to_check.bound = OperatorBound(pc.Relation.LESS, threshold)
        hypothesis = "allviolated" if safe else "allsat"

        _, resultfile = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)

        constants_string = self.constants.to_key_value_string(to_float=False) if self.constants else ""

        args = [self.parameter_location,
                '--prism', self.prismfile.location,
                '--prop', str(property_to_check),
                '--region', region_string,
                '--hypothesis', hypothesis,
                '--resultfile', resultfile,
                '--noillustration'
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
        with open(resultfile) as f:
            for line in f:
                line = line.strip()
                if line[-1] != ";":
                    raise ValueError("Expect line to end with a semicolon")
                line = line[:-1]
                res_line = line.split(":")
                if len(res_line) != 2:
                    raise ValueError("Unexpected content in result file")
                if res_line[0] == "AllViolated":
                    if hypothesis == "allviolated":
                        region_result = RegionCheckResult.Satisfied
                    else:
                        assert hypothesis == "allsat"
                        raise RuntimeError("Contradiction of hypothesis")
                elif res_line[0] == "AllSat":
                    if hypothesis == "allsat":
                        region_result = RegionCheckResult.Satisfied
                    else:
                        assert hypothesis == "allviolated"
                        raise RuntimeError("Contradiction of hypothesis")
                elif res_line[0] == "ExistsBoth":
                    raise RuntimeError("Unexpected outcome, something went wrong.")
                elif res_line[0] == "Unknown":
                    region_result = RegionCheckResult.Unknown
                elif res_line[0] == "CenterSat" or res_line[0] == "CenterViolated":
                    logger.warning("Center sat is not expected.")
                    region_result = RegionCheckResult.Unknown

                else:
                    raise RuntimeError("Unexpected content '{}' in result file".format(res_line[0]))

                region_string_out = res_line[1].strip()
                region = HyperRectangle.from_region_string(region_string_out, parameters.get_variables())
                regions.append((region_result, region))
        return regions
