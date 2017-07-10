import os
import subprocess
import tempfile
import logging

from prophesy.config import configuration
from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.modelcheckers.pmc import BisimulationType
from prophesy.input.samplefile import read_samples_file
from prophesy.util import run_tool, ensure_dir_exists, write_string_to_tmpfile
from prophesy.data.samples import InstantiationResultDict, InstantiationResult
from prophesy.data.constant import Constants
from prophesy.adapter.pycarl import Rational
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError
import prophesy.data.range

logger = logging.getLogger(__name__)


class PrismModelChecker(ParametricProbabilisticModelChecker):
    def __init__(self, location=configuration.get_prism()):
        self.location = location
        self.bisimulation = BisimulationType.strong
        self.pctlformula = None
        self.prismfile = None
        self.constants = None

    def name(self):
        return "prism"

    def version(self):
        args = [self.location, '-version']
        return run_tool(args, True)

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
        file, resultfile = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)

        constants_string = self.constants.to_key_value_string()

        args = [self.location,
                self.prismfile.location,
                '--pctl', str(self.pctlformula),
                '-exportresults', resultfile,
                '-paramelimorder', 'fwrev']
        if self.bisimulation == BisimulationType.strong:
            args.append('-parambisim')
            args.append('strong')
        if constants_string != "":
            args.append('-const')
            args.append(constants_string)
        variables = self.prismfile.parameters.get_variables()
        args.append('-param')
        args.append('"{}"'.format(', '.join([str(var) for var in variables])))

        logger.info("Call prism")
        ret_code = run_tool(args, False)
        if ret_code != 0:
            # TODO throw exception?
            logger.warning("Return code %s after call with %s", ret_code, " ".join(args))
        else:
            logger.info("Prism call finished successfully")

        # TODO: return result in correct format
        result = ""
        with open(resultfile, 'r') as f:
            result += f.read() + "\n";
        os.remove(resultfile)
        logger.debug("Result: {}".format(result))

        raise NotImplementedError("Writing of prism result is not implemented")
        return None

    def perform_uniform_sampling(self, parameters, samples_per_dimension):
        logger.info("Perform uniform sampling")
        if self.pctlformula is None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile is None: raise NotEnoughInformationError("model missing")
        assert len(self.prismfile.parameters) - len(self.constants) == len(parameters.get_variables()), "Number of intervals does not match number of parameters"
        assert samples_per_dimension > 1
        ranges = [prophesy.data.range.create_range_from_interval(interval, samples_per_dimension) for interval in parameters.get_variable_bounds()]

        range_strings = ["{0}:{1}:{2}".format(r.start, r.step, r.stop) for r in ranges]
        const_values_string = ",".join(["{0}={1}".format(p, r) for (p, r) in zip(parameters.get_variables(), range_strings)])
        constants_string = self.constants.to_key_value_string(to_float = True)
        if constants_string != "":
            const_values_string = const_values_string + "," + constants_string

        ensure_dir_exists(configuration.get_intermediate_dir())
        _, resultpath = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)
        pctlpath = write_string_to_tmpfile(str(self.pctlformula))

        args = [self.location, self.prismfile.location, pctlpath,
                "-const", const_values_string,
                "-exportresults", resultpath]
        logger.info("Call prism")
        ret_code = run_tool(args)
        if ret_code != 0:
            logger.warning("Return code %s after call with %s", ret_code, " ".join(args))
        else:
            logger.info("Prism call finished successfully")
        found_parameters, _, samples = read_samples_file(resultpath, parameters)

        os.remove(resultpath)
        os.remove(pctlpath)
        return samples

    def perform_sampling(self, samplepoints):
        if self.pctlformula is None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile is None: raise NotEnoughInformationError("model missing")

        ensure_dir_exists(configuration.get_intermediate_dir())
        _, resultpath = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)
        pctlpath = write_string_to_tmpfile(str(self.pctlformula))

        print(samplepoints.parameters)

        samples = InstantiationResultDict(samplepoints.parameters)
        for sample_point in samplepoints:
            const_values_string = ",".join(["{0}={1}".format(parameter.variable, float(val)) for parameter, val in sample_point.items()])
            constants_string = self.constants.to_key_value_string(to_float=True)
            if constants_string != "":
                const_values_string = const_values_string + "," + constants_string

            args = [self.location, self.prismfile.location, pctlpath,
                    "-const", const_values_string,
                    "-exportresults", resultpath]
            logger.info("Call prism...")
            ret_code = run_tool(args)
            if ret_code != 0:
                logger.warning("Return code %s after call with %s", ret_code, " ".join(args))
            else:
                logger.info("Prism call finished successfully")
            with open(resultpath) as f:
                f.readline()
                tmp = f.readline()
                assert tmp is not None
                assert tmp != ""
                sample_value = Rational(tmp)

            samples.add_result(InstantiationResult(sample_point, sample_value))
        os.remove(resultpath)
        os.remove(pctlpath)
        return samples
