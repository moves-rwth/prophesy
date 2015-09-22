import configparser
import util
import os

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

configuration = Configuration()
# section names
EXTERNAL_TOOLS = "external_tools"
DIRECTORIES = "directories"

# CONSTANTS
TOOLNAME = "prophesy"
VERSION = [0, 3, 0]
SUPPORT = ["Nils Jansen, Sebastian Junges"]
PRECISION = 0.0001