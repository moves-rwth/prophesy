import pytest

from tornado_test_case import TornadoTestCase

# Imported to start the webservice and check it's functionality
from prophesy_web.application import make_app, initEnv
from tornado.testing import AsyncHTTPTestCase

# For parsing json-strings in dicts
import json

# To create random numbers for testing the configuration (maybe unnecessary)
import random

# Check if a file really exists
import os.path
import shutil

from helpers.helper import get_example_path

# Get the prophesy configuration data
import prophesy.config as config
from prophesy.config import configuration
from prophesy_web.config import configuration as web_configuration


@pytest.mark.skipif(not web_configuration.is_redis_running(), reason="requires running redis instance")
@pytest.mark.incremental
class TestTornado(TornadoTestCase):
    """ Testing of the workflow in Prophesy. """

    def test_0_storm_available(self):
        if configuration.get_storm() is None:
            print("WARINING: Not all tests are correct. Storm was not found!!!")
            assert 0

    def test_1_upload_files(self):
        with open(get_example_path("brp", "brp_16-2.pm"), 'r') as pfile:
            prismdata = pfile.read()
        with open(get_example_path("brp", "property1.pctl"), 'r') as pfile:
            pctldata = pfile.read()
        with open(get_example_path("brp", "brp_16-2.rat"), 'r') as pfile:
            result_data = pfile.read()
        prismfile = ('prism-file', 'brp_16-2.pm', prismdata)
        pctlfile = ('pctl-file', 'property1.pctl', pctldata)
        result_file = ('result-file', 'brp_16-2.rat', result_data)
        ct, data = self._encode_multipart_formdata([], [prismfile])
        response = self._sendData('/uploadPrism', data=data, ct=ct)
        assert response.code == 200
        ct, data = self._encode_multipart_formdata([], [pctlfile])
        response = self._sendData('/uploadPctl', data=data, ct=ct)
        assert response.code == 200
        ct, data = self._encode_multipart_formdata([("result-type", "storm")], [result_file])
        response = self._sendData('/uploadResult', data=data, ct=ct)
        assert response.code == 200

    def test_2_run_with_storm(self):
        self.test_1_upload_files()
        ct, data = self._encode_multipart_formdata(
            [("prism", "brp_16-2.pm"), ("pctl_group", "property1.pctl"), ("pctl_property", "P=? [F \"target\"]"),
             ("mctool", "storm")], [])
        response = self._sendData('/runPrism', data, ct)
        print(response)
        assert response.code == 200

    def test_3_sampling(self):
        self.test_2_run_with_storm()
        ct, data = self._encode_multipart_formdata([("pmc", "storm"), ("sampler", "ratfunc"), ("sat", "z3")], [])
        response = self._sendData('/environment', data, ct)
        samples = '[["0.00","0.00"],["0.50","0.50"],["1.00","1.00"]]'
        response = self._sendData('/samples', samples, "application/json")
        print(response.body.decode("UTF-8"))
        assert response.code == 200
