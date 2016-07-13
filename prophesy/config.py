import prophesy.util as util
import os
from prophesy.util import Configuration
from prophesy.exceptions.configuration_error import ConfigurationError

class ProphesyConfig(Configuration):
    # section names
    DIRECTORIES = "directories"
    EXTERNAL_TOOLS = "external_tools"
    SAMPLING = "sampling"
    CONSTRAINTS = "constraints"
    DEPENDENCIES = "installed_deps"

    def __init__(self):
        super().__init__(os.path.join(os.path.dirname(
                os.path.realpath(__file__)), "prophesy.cfg"))
        self._init_tools()

    def is_module_available(self, module):
        try:
            return self.getboolean(ProphesyConfig.DEPENDENCIES, module)
        except ConfigurationError:
            return False

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
        return self.samplers

    def _init_tools(self):
        self.smtsolvers = set()
        self.pmcs = set()
        self.ppmcs = set()
        self.samplers = dict()

        storm_loc = self.get_storm()
        if storm_loc:
            try:
                util.run_tool([storm_loc], True)
                self.ppmcs.add('storm')
                self.pmcs.add('storm')
                #TODO check whether this is really storm
            except:
                raise ConfigurationError("Storm is not found at " + storm_loc)

        prism_loc = self.get_prism()
        if prism_loc:
            try:
                util.run_tool([prism_loc], True)
                self.ppmcs.add('prism')
                self.pmcs.add('prism')
                #self.samplers.add('prism')
            except:
                raise ConfigurationError("Prism is not found at " + prism_loc)

        param_loc = self.get_param()
        if param_loc:
            try:
                util.run_tool([param_loc], True)
                self.ppmcs.add('param')
            except:
                raise ConfigurationError("Param is not found at " + param_loc)

        z3_loc = self.get_z3()
        if z3_loc:
            try:
                util.run_tool([z3_loc], True)
                self.smtsolvers.add('z3')
            except:
                raise ConfigurationError("Z3 is not found at " + z3_loc)

        isat_loc = self.get_isat()
        if isat_loc:
            try:
                util.run_tool([isat_loc], True)
                self.smtsolvers.add('isat')
            except:
                raise ConfigurationError("ISat is not found at " + isat_loc)

        if self.is_module_available("stormpy"):
            self.pmcs.add('stormpy')
            self.ppmcs.add('stormpy')

        self.samplers['ratfunc'] = "Rational function"

    def get_storm(self):
        tool_loc = self.get(ProphesyConfig.EXTERNAL_TOOLS, "storm")
        return tool_loc if tool_loc else None

    def get_prism(self):
        tool_loc = self.get(ProphesyConfig.EXTERNAL_TOOLS, "prism")
        return tool_loc if tool_loc else None

    def get_param(self):
        tool_loc = self.get(ProphesyConfig.EXTERNAL_TOOLS, "param")
        return tool_loc if tool_loc else None

    def get_z3(self):
        tool_loc = self.get(ProphesyConfig.EXTERNAL_TOOLS, "z3")
        return tool_loc if tool_loc else None

    def get_isat(self):
        tool_loc = self.get(ProphesyConfig.EXTERNAL_TOOLS, "isat")
        return tool_loc if tool_loc else None

    def get_intermediate_dir(self):
        return self.get(ProphesyConfig.DIRECTORIES, "intermediate_files")

    def get_plots_dir(self):
        return self.get(ProphesyConfig.DIRECTORIES, "plots")

    def get_sampling_min_distance(self):
        # Minimum distance between points to allow further sampling
        return float(self.get(ProphesyConfig.SAMPLING, "distance"))

    def get_sampling_epsilon(self):
        # Smallest discernable difference for intervals (used for strict bounds)
        return 0.0125
        return float(self.get(ProphesyConfig.SAMPLING, "epsilon"))

    def get_regions_precision(self):
        # Epsilon for ofsetting region bounds (e.g., for sampling inside a region)
        return float(self.get(ProphesyConfig.CONSTRAINTS, "precision"))

configuration = ProphesyConfig()

TOOLNAME = "prophesy"
VERSION = [0, 3, 0]
SUPPORT = ["Nils Jansen, Sebastian Junges, Matthias Volk"]
