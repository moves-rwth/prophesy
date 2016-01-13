from distutils.spawn import find_executable

import configparser
import util
import os

from exceptions.configuration_error import ConfigurationError

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

    def set(self, section, key):
        if(self._importedFrom == ""):
            self._importFromFile()
        assert()

    def updateConfigurationFile(self):
        with open(self._importedFrom, 'w') as f:
            self._config.write(f)

    def getAvailableSMTSolvers(self):
        smtsolvers = set()

        # finding executables is a job for write_config.
        z3Loc =  configuration.get(EXTERNAL_TOOLS, "z3")
        if z3Loc != "":
            try:
                util.run_tool([z3Loc], True)
                smtsolvers.add('z3')
                #TODO check whether this is really z3
            except:
                raise ConfigurationError("Z3 is not found at " + z3Loc)

        isatLoc =  configuration.get(EXTERNAL_TOOLS, "isat")
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
        stormLoc =  configuration.get(EXTERNAL_TOOLS, "storm")
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

        if configuration.get(DEPENDENCIES, "stormpy"):
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

        if configuration.get(DEPENDENCIES, "stormpy"):
            ppmcs.add('stormpy')

        if len(ppmcs) == 0:
            raise RuntimeError("No model checkers in environment")
        return ppmcs

    def getAvailableSamplers(self):
        samplers = {}
        samplers['ratfunc'] = "Rational function"
        samplers['ratfunc_float'] = "Rational function (float)"
        if configuration.get(DEPENDENCIES, "pycarl"):
            samplers['carl'] = "Carl library"

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
PRECISION = float(configuration.get(CONSTRAINTS, "precision"))

# CONSTANTS
TOOLNAME = "prophesy"
VERSION = [0, 3, 0]
SUPPORT = ["Nils Jansen, Sebastian Junges, Matthias Volk"]
