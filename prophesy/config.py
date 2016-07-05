import configparser
import prophesy.util as util
import os

from prophesy.exceptions.configuration_error import ConfigurationError

class Configuration():
    def __init__(self):
        self._config = configparser.ConfigParser()
        self._importedFrom = ""
        self.modified = False

    def _importFromFile(self):
        location = os.path.join(os.path.dirname(os.path.realpath(__file__)), "prophesy.cfg")
        util.check_filepath_for_reading(location, "configuration file")
        self._config.read(location)
        self._importedFrom = location


    def get(self, section, key):
        if self._importedFrom == "":
            self._importFromFile()
        assert section in self._config
        assert key in self._config[section]
        return self._config[section][key]

    def is_module_available(self, module):
        if self._importedFrom == "":
            self._importFromFile()
        assert DEPENDENCIES in self._config
        assert module in self._config[DEPENDENCIES]
        return self._config.getboolean(DEPENDENCIES, module)

    # TODO: REPAIR THIS
    def getAll(self):
        if self._importedFrom == "":
            self._importFromFile()
        # Convert configuration into dict of dicts
        # where each section has its own dictionary with (key,value)
        result = {}
        sections = self._config.sections()
        for section in sections:
            result[section] = dict(self._config.items(section))
        return result

    def set(self, section, key, value):
        if(self._importedFrom == ""):
            self._importFromFile()
        assert section in self._config
        assert key in self._config[section]
        self._config.set(section, key, value)
        self.modified = True

    def updateConfigurationFile(self):
        with open(self._importedFrom, 'w') as f:
            self._config.write(f)

    def getAvailableSMTSolvers(self):
        smtsolvers = set()

        # finding executables is a job for write_config.
        z3Loc = configuration.get(EXTERNAL_TOOLS, "z3")
        if z3Loc != "":
            try:
                util.run_tool([z3Loc], True)
                smtsolvers.add('z3')
                #TODO check whether this is really z3
            except:
                raise ConfigurationError("Z3 is not found at " + z3Loc)

        isatLoc = configuration.get(EXTERNAL_TOOLS, "isat")
        if isatLoc != "":
            try:
                util.run_tool([isatLoc], True)
                smtsolvers.add('isat')
                #TODO check whether this is really isat
            except:
                raise ConfigurationError("Isat is not found at " + isatLoc)

        if len(smtsolvers) == 0:
            raise RuntimeError("No SMT solvers in environment")
        return smtsolvers

    def getAvailableProbMCs(self):
        pmcs = set()
        stormLoc = configuration.get(EXTERNAL_TOOLS, "storm")
        if stormLoc != "":
            try:
                util.run_tool([stormLoc], True)
                pmcs.add('storm')
                #TODO check whether this is really storm
            except:
                raise ConfigurationError("Storm is not found at " + stormLoc)

        prismLoc = configuration.get(EXTERNAL_TOOLS, "prism")
        if prismLoc != "":
            try:
                util.run_tool([configuration.get(EXTERNAL_TOOLS, "prism")], True)
                pmcs.add('prism')
            except:
                raise ConfigurationError("Prism is not found at " + prismLoc)

        if configuration.is_module_available("stormpy"):
            pmcs.add('stormpy')

        if len(pmcs) == 0:
            raise RuntimeError("No model checkers in environment")
        return pmcs

    def getAvailableParametricMCs(self):
        """
        :return: A set with strings describing the available parametric pmcs.
        """
        ppmcs = set()
        paramLoc = configuration.get(EXTERNAL_TOOLS, "param")
        if paramLoc != "":
            try:
                util.run_tool([paramLoc], True)
                ppmcs.add('param')
                #TODO check whether this is really param
            except:
                raise ConfigurationError("Param not found at " + paramLoc)

        stormLoc = configuration.get(EXTERNAL_TOOLS, "storm")
        if stormLoc != "":
            try:
                util.run_tool([stormLoc], True)
                ppmcs.add('storm')
                #TODO check whether this is really storm
            except:
                raise ConfigurationError("Storm is not found at " + stormLoc)

        prismLoc = configuration.get(EXTERNAL_TOOLS, "prism")
        if prismLoc != "":
            try:
                util.run_tool([configuration.get(EXTERNAL_TOOLS, "prism")], True)
                ppmcs.add('prism')
            except:
                raise ConfigurationError("Prism is not found at " + prismLoc)

        if configuration.is_module_available("stormpy"):
            ppmcs.add('stormpy')

        if len(ppmcs) == 0:
            raise RuntimeError("No model checkers in environment")
        return ppmcs

    def getAvailableSamplers(self):
        samplers = {}
        samplers['ratfunc'] = "Rational function"

        try:
            # TODO: Prism sampling not yet supported
            # util.run_tool([PRISM_COMMAND], True)
            # samplers['prism'] = "PRISM"
            # print("Found prism")
            pass
        except:
            pass

        if len(samplers) == 0:
            raise RuntimeError("No samplers in environment")
        return samplers

configuration = Configuration()


# directories
DIRECTORIES = "directories"
INTERMEDIATE_FILES = configuration.get(DIRECTORIES, "intermediate_files")
PLOTS = configuration.get(DIRECTORIES, "plots")
WEB_RESULTS = configuration.get(DIRECTORIES, "web_results")


# section names
EXTERNAL_TOOLS = "external_tools"
SAMPLING = "sampling"
CONSTRAINTS = "constraints"
DEPENDENCIES = "installed_deps"


# CONSTANTS
# Smallest discernable difference for intervals (used for strict bounds)
INTERVAL_EPSILON = 0.01
PRECISION = float(configuration.get(CONSTRAINTS, "precision"))
# Minimum distance between points to allow further sampling
DISTANCE = float(configuration.get(SAMPLING, "distance"))
TOOLNAME = "prophesy"
VERSION = [0, 3, 0]
SUPPORT = ["Nils Jansen, Sebastian Junges, Matthias Volk"]
