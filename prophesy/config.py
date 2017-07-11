import os
import logging
import re

import prophesy.util as util
from prophesy.adapter.pycarl import Integer, Rational
from prophesy.util import Configuration
from prophesy.exceptions.configuration_error import ConfigurationError


class ProphesyConfig(Configuration):
    # section names
    DIRECTORIES = "directories"
    EXTERNAL_TOOLS = "external_tools"
    SAMPLING = "sampling"
    CONSTRAINTS = "constraints"
    DEPENDENCIES = "installed_deps"
    SMT = "smt"

    def __init__(self):
        super().__init__(os.path.join(os.path.dirname(
                os.path.realpath(__file__)), "prophesy.cfg"))
        self._init_tools()

    def is_module_available(self, module):
        return self.get_boolean(ProphesyConfig.DEPENDENCIES, module)

    def getAvailableSMTSolvers(self):
        if len(self.smtsolvers) == 0:
            raise RuntimeError("No SMT solvers in environment")
        return self.smtsolvers

    def getAvailableProbMCs(self):
        if len(self.pmcs) == 0:
            raise RuntimeError("No model checkers in environment")
        return self.pmcs

    def getAvailableParametricMCs(self):
        """
        :return: A set with strings describing the available parametric pmcs.
        """
        if len(self.ppmcs) == 0:
            raise RuntimeError("No model checkers in environment")
        return self.ppmcs

    def getAvailableSamplers(self):
        if len(self.samplers) == 0:
            raise RuntimeError("No sampler in environment")
        return self.samplers

    def _init_tools(self):
        self.smtsolvers = set()
        self.pmcs = set()
        self.ppmcs = set()
        self.samplers = dict()

        storm_loc = self.get_storm()
        if storm_loc:
            self.ppmcs.add('storm')
            self.pmcs.add('storm')
            self.samplers['storm'] = storm_loc  # TODO Just store 'storm'?

        if self.get_storm_pars():
            self.ppmcs.add('storm-pars')

        if self.get_prism():
            self.ppmcs.add('prism')
            self.pmcs.add('prism')
            #self.samplers.add('prism')

        if self.get_param():
            self.ppmcs.add('param')

        if self.get_z3():
            self.smtsolvers.add('z3')

        if self.get_yices():
            self.smtsolvers.add('yices')

        if self.get_isat():
            self.smtsolvers.add('isat')

        if self.is_module_available("stormpy"):
            self.pmcs.add('stormpy')
            self.ppmcs.add('stormpy')

        self.samplers['ratfunc'] = "Rational function"

    def check_tools(self):
        storm_loc = self.get_storm()
        if storm_loc:
            try:
                output = util.run_tool([storm_loc, '--version'], True)
            except:
                raise ConfigurationError("Storm is not found at " + storm_loc)
            if not re.match(r"Storm ", output, re.MULTILINE):
                raise ConfigurationError("Storm is not found at " + storm_loc)

        storm_loc = self.get_storm_pars()
        if storm_loc:
            try:
                output = util.run_tool([storm_loc, '--version'], True)
            except:
                raise ConfigurationError("Storm-pars is not found at " + storm_loc)
            if not re.match(r"Storm-pars", output, re.MULTILINE):
                raise ConfigurationError("Storm-pars is not found at " + storm_loc)

        prism_loc = self.get_prism()
        if prism_loc:
            try:
                output = util.run_tool([prism_loc, '--version'], True)
            except:
                raise ConfigurationError("Prism is not found at " + prism_loc)
            if not re.match(r"PRISM", output, re.MULTILINE):
                raise ConfigurationError("Prism is not found at " + prism_loc)

        param_loc = self.get_param()
        if param_loc:
            # TODO check param similar to other tools
            try:
                util.run_tool([param_loc], True)
            except:
                raise ConfigurationError("Param is not found at " + param_loc)

        z3_loc = self.get_z3()
        if z3_loc:
            try:
                output = util.run_tool([z3_loc, '--version'], True)
            except:
                raise ConfigurationError("Z3 is not found at " + z3_loc)
            if not re.match(r"Z3", output, re.MULTILINE):
                raise ConfigurationError("Z3 is not found at " + z3_loc)

        yices_loc = self.get_yices()
        if yices_loc:
            # TODO check yices similar to other tools
            try:
                util.run_tool([yices_loc, '-h'], True)
            except:
                raise ConfigurationError("Yices is not found at " + yices_loc)

        isat_loc = self.get_isat()
        if isat_loc:
            # TODO check isat similar to other tools
            try:
                util.run_tool([isat_loc], True)
            except:
                raise ConfigurationError("ISat is not found at " + isat_loc)

    def get_tool(self, toolname):
        tool_loc = self.get(ProphesyConfig.EXTERNAL_TOOLS, toolname)
        return os.path.expanduser(tool_loc) if tool_loc else None

    def get_storm(self):
        return self.get_tool("storm")

    def get_storm_pars(self):
        return self.get_tool("storm-pars")

    def get_prism(self):
        return self.get_tool("prism")

    def get_param(self):
        return self.get_tool("param")

    def get_z3(self):
        return self.get_tool("z3")

    def get_yices(self):
        return self.get_tool("yices")

    def get_isat(self):
        return self.get_tool("isat")

    def has_stormpy(self):
        return self.is_module_available("stormpy")

    def get_intermediate_dir(self):
        dir = self.get(ProphesyConfig.DIRECTORIES, "intermediate_files")
        util.ensure_dir_exists(dir)
        return dir

    def get_plots_dir(self):
        dir = self.get(ProphesyConfig.DIRECTORIES, "plots")
        util.ensure_dir_exists(dir)
        return dir

    def get_sampling_min_distance(self):
        # Minimum distance between points to allow further sampling
        return self.get_float(ProphesyConfig.SAMPLING, "distance")

    def get_sampling_epsilon(self):
        # Smallest discernable difference for intervals (used for strict bounds)
        return Rational(Integer(1), Integer(800))
        # TODO why is the following commented out.
        # return self.get_float(ProphesyConfig.SAMPLING, "epsilon")

    def get_regions_precision(self):
        # Epsilon for ofsetting region bounds (e.g., for sampling inside a region)
        return self.get_float(ProphesyConfig.CONSTRAINTS, "precision")

    def get_smt_timeout(self):
        return self.get_float(ProphesyConfig.SMT, "timeout")

    def getSection(self, sec):
        return self.getAll()[sec]

configuration = ProphesyConfig()

# TODO Put in config
TOOLNAME = "prophesy"
VERSION = [0, 3, 0]
SUPPORT = ["Nils Jansen, Sebastian Junges, Matthias Volk"]

logging.basicConfig(filename='prophesy.log', level=logging.DEBUG)
logging.basicConfig(format='%(levelname)s:%(message)s', level=logging.DEBUG)
ch = logging.StreamHandler()
ch.setLevel(logging.INFO)
logging.getLogger().addHandler(ch)
