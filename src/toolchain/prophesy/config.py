import configparser
import util
import os
from distutils.spawn import find_executable

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
        smtsolvers = []
        try:
            find_executable(configuration.get(EXTERNAL_TOOLS, "z3"))
            smtsolvers.append("z3")
            print("Found z3")
        except:
            pass
        try:
            util.run_tool(configuration.get(EXTERNAL_TOOLS, "smtrat"), True)
            smtsolvers.append("smtrat")
            print("Found smtrat")
        except:
            pass

        if len(smtsolvers) == 0:
            raise RuntimeError("No SMT solvers in environment")
        return smtsolvers

    def getAvailableSamplers(self):
        ppmcCheckers = {}
        try:
            util.run_tool([configuration.get(EXTERNAL_TOOLS, "param")], True)
            ppmcCheckers['param'] = "Param"
            print("Found param")
        except:
            pass
        try:
            util.run_tool([configuration.get(EXTERNAL_TOOLS, "storm")], True)
            ppmcCheckers['pstorm'] = "Parametric Storm"
            print("Found pstorm")
        except:
            pass

        if len(ppmcCheckers) == 0:
            raise RuntimeError("No model checkers in environment")
        return ppmcCheckers

    def getAvailableParametricMCs(self):
        samplers = {}
        samplers['ratfunc'] = "Rational function"
        samplers['ratfunc_float'] = "Rational function (float)"
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
# section names
EXTERNAL_TOOLS = "external_tools"
DIRECTORIES = "directories"

# CONSTANTS
TOOLNAME = "prophesy"
VERSION = [0, 3, 0]
SUPPORT = ["Nils Jansen, Sebastian Junges, Matthias Volk"]
PRECISION = 0.0001
