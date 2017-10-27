import os
import tempfile
import logging

from prophesy.config import configuration
from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker
from prophesy.modelcheckers.pmc import BisimulationType
from prophesy.input.samplefile import read_samples_file
from prophesy.util import run_tool, ensure_dir_exists, write_string_to_tmpfile
from prophesy.data.samples import InstantiationResultDict
from prophesy.data.constant import Constants
from prophesy.adapter.pycarl import Rational
from prophesy.exceptions.not_enough_information_error import NotEnoughInformationError
import prophesy.data.range

logger = logging.getLogger(__name__)


class PrismModelChecker(ParametricProbabilisticModelChecker):
    """
    Class wrapping the prism model checker CLI.
    """

    def __init__(self, location=configuration.get_prism()):
        """
        Constructor
        :param location: Path to prism binary.
        """
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

    def set_bisimulation_type(self, bisimulationType):
        assert (isinstance(bisimulationType, BisimulationType))
        self.bisimulation = bisimulationType

    def set_pctl_formula(self, formula):
        self.pctlformula = formula

    def load_model_from_prismfile(self, prismfile, constants=Constants()):
        self.prismfile = prismfile
        self.constants = constants

    def load_model_from_drn(self, drnfile, constants=Constants()):
        raise RuntimeError("Prism does not support DRN")

    def get_parameter_constraints(self):
        raise NotImplementedError("Generating constraints for parameters in prism is not implemented.")

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
        args.append('-param')
        args.append('{}'.format(','.join([p.name for p in self.prismfile.parameters])))

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
            result += f.read() + "\n"
        os.remove(resultfile)
        logger.debug("Result: {}".format(result))

        raise NotImplementedError("Writing of prism result is not implemented")

    def perform_uniform_sampling(self, parameters, samples_per_dimension):
        logger.info("Perform uniform sampling")
        if self.pctlformula is None: raise NotEnoughInformationError("pctl formula missing")
        if self.prismfile is None: raise NotEnoughInformationError("model missing")
        assert len(self.prismfile.parameters) == len(parameters), "Number of intervals does not match number of parameters"
        assert samples_per_dimension > 1
        ranges = [prophesy.data.range.create_range_from_interval(interval, samples_per_dimension) for interval in
                  parameters.get_parameter_bounds()]

        range_strings = ["{0}:{1}:{2}".format(float(r.start), float(r.step), float(r.stop)) for r in ranges]
        const_values_string = ",".join(["{}={}".format(v.name, r) for v, r in zip(parameters, range_strings)])
        constants_string = self.constants.to_key_value_string()
        if constants_string != "":
            const_values_string = const_values_string + "," + constants_string

        ensure_dir_exists(configuration.get_intermediate_dir())
        fd, resultpath = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)
        os.close(fd)
        pctlpath = write_string_to_tmpfile(str(self.pctlformula))

        args = [self.location,
                self.prismfile.location,
                pctlpath,
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
        fd, result_path = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)
        pctl_path = write_string_to_tmpfile(str(self.pctlformula))
        os.close(fd)

        samples = InstantiationResultDict({s: self.sample_single_point(s, result_path, pctl_path) for s in samplepoints})

        os.remove(result_path)
        os.remove(pctl_path)
        return samples

    def sample_single_point(self, parameter_instantiation, result_path=None, pctl_path=None):
        if result_path is None:
            _, result_path = tempfile.mkstemp(suffix=".txt", dir=configuration.get_intermediate_dir(), text=True)
        if pctl_path is None:
            pctl_path = write_string_to_tmpfile(str(self.pctlformula))

        const_values_string = ",".join(["{}={}".format(parameter.name, float(val)) for parameter, val in parameter_instantiation.items()])
        constants_string = self.constants.to_key_value_string()
        if constants_string != "":
            const_values_string = const_values_string + "," + constants_string

        args = [self.location, self.prismfile.location, pctl_path,
                "-const", const_values_string,
                "-exportresults", result_path]
        logger.info("Call prism...")
        ret_code = run_tool(args)
        if ret_code != 0:
            logger.warning("Return code %s after call with %s", ret_code, " ".join(args))
        else:
            logger.info("Prism call finished successfully")
        with open(result_path) as f:
            f.readline()
            tmp = f.readline()
            assert tmp is not None
            assert tmp != ""
            sample_value = Rational(tmp)
            return sample_value

    def check_hyperrectangle(self, parameters, hyperrectangle, threshold, above_threshold):
        raise NotImplementedError("Checking of hyperrectangles with prism is not implemented.")
