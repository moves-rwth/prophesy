from tornado_test_case import TornadoTestCase

# For parsing json-strings in dicts
import json

# To create random numbers for testing the configuration (maybe unnecessary)
import random

# Check if a file really exists
import os.path
import shutil

# Get the prophesy configuration data
import prophesy.config as config
from prophesy.config import configuration


class TestTornado(TornadoTestCase):
    """ Testing of the tornado web framework. """
    
    def test_homepage(self):
        """ Test if the prophesy homepage is available. """
        response = self.fetch('/')
        self.assertEqual(response.code, 200)

    def test_config(self):
        """ Test if the configuration webinterface can change the values of the config-file. """

        # Create random new test value
        new_value = str(random.random())
        value_before = self._get_response_string('/config/test/test_value')
        while new_value == value_before:
            new_value = str(random.random())

        # Change value
        body_send = "data=" + new_value
        response = self._sendData('/config/test/test_value', body_send)
        self.assertEqual(response.code, 200)
        s = response.body.decode('UTF-8')

        # Check new value
        response = self.fetch('/config/test/test_value')
        s = response.body.decode('UTF-8')
        value_after = json.loads(s)["data"]
        self.assertNotEqual(value_before, value_after)
        self.assertEqual(value_after, new_value)

    def test_directories(self):
        """ Checks if the directories of the config file exist. """
        section = configuration.getSection(config.DIRECTORIES)
        for directory in section:
            os.path.isdir(directory)

    def test_executables(self):
        """ Checks if the executables exist"""
        section = configuration.getSection(config.EXTERNAL_TOOLS)
        for tool in section:
            if not section[tool] == '':
                assert (os.path.isfile(section[tool]) == "True") or (shutil.which(section[tool]) is not None)
