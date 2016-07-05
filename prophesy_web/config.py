import configparser
import os

import prophesy.util as util
from prophesy.exceptions.configuration_error import ConfigurationError

class Configuration():
    def __init__(self):
        self._config = configparser.ConfigParser()
        self._importedFrom = ""
        self.modified = False

    def _importFromFile(self):
        location = os.path.join(os.path.dirname(os.path.realpath(__file__)), "prophesy_web.cfg")
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

configuration = Configuration()


# directories
DIRECTORIES = "directories"
WEB_RESULTS = configuration.get(DIRECTORIES, "web_results")

TOOLNAME = "prophesy_web"
VERSION = [0, 0, 1]
SUPPORT = ["Nils Jansen, Sebastian Junges, Matthias Volk"]
