from tornado_test_case import TornadoTestCase

# For parsing json-strings in dicts
import json

# To create random numbers for testing the configuration (maybe unnecessary)
import random

# Check if a file really exists
import os.path
import shutil
from helpers.helper import get_example_path

# Get the prophesy configuration data
import prophesy.config as config # This imports the Class data file
from prophesy.config import configuration # This imports the instanciated Object of 'ProphesyConfig'


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
        value_before = self._get_response_string('/config/directories/plots')
        while new_value == value_before:
            new_value = str(random.random())

        # Change value
        body_send = "data=" + new_value
        response = self._sendData('/config/directories/plots', body_send)
        self.assertEqual(response.code, 200)
        s = response.body.decode('UTF-8')

        # Check new value
        response = self.fetch('/config/directories/plots')
        s = response.body.decode('UTF-8')
        value_after = json.loads(s)["data"]
        self.assertNotEqual(value_before, value_after)
        self.assertEqual(value_after, new_value)

    def test_directories(self):
        """ Checks if the directories of the config file exist. """
        section = configuration.getSection(configuration.DIRECTORIES)
        for directory in section:
            os.path.isdir(directory)

    def test_executables(self):
        """ Checks if the executables exist"""
        section = configuration.getSection(configuration.EXTERNAL_TOOLS)
        for tool in section:
            if not section[tool] == '':
                assert (os.path.isfile(section[tool]) == "True") or (shutil.which(section[tool]) is not None)

    def test_upload_files(self):
        with open(get_example_path("pdtmc", "brp", "brp_16_2.pm"), 'r') as pfile:
            prismdata = pfile.read()
        with open(get_example_path("pdtmc", "brp", "property1.pctl"), 'r') as pfile:
            pctldata = pfile.read()
        with open(get_example_path("examples", "brp", "brp_16-2.rat"), 'r') as pfile:
            result_data = pfile.read()
        prismfile = ('prism-file', 'brp_16_2.pm', prismdata)
        pctlfile = ('pctl-file', 'property1.pctl', pctldata)
        result_file = ('result-file', 'results_w_bisim.res', result_data)
        ct, data = self.encode_multipart_formdata([], [prismfile])
        response = self._sendData('/uploadPrism', data=data, ct=ct)
        assert response.code == 200
        ct, data = self.encode_multipart_formdata([], [pctlfile])
        response = self._sendData('/uploadPctl', data=data, ct=ct)
        assert response.code == 200
        ct, data = self.encode_multipart_formdata([("result-type","storm")], [result_file])
        response = self._sendData('/uploadResult', data=data, ct=ct)
        assert response.code == 200

    def test_run_with_storm(self):
        self.test_upload_files()
        ct, data = self.encode_multipart_formdata([("prism","brp_16_2.pm"),("pctl_group", "property1.pctl"),("pctl_property", "P=? [F \"target\"]"),("mctool", "storm")], [])
        response = self._sendData('/runPrism', data, ct)
        assert response.code == 200

    def test_sampling(self):
        self.test_run_with_storm()
        ct, data = self.encode_multipart_formdata([("pmc","storm"),("sampler","ratfunc"),("sat","z3")], [])
        response = self._sendData('/environment', data, ct)
        samples = '[["0.00","0.00"],["0.50","0.50"],["1.00","1.00"]]'
        response = self._sendData('/samples', samples, "application/json")
        print(response.body.decode("UTF-8"))
        assert response.code == 200

    def test_auto_sample(self):
        self.test_run_with_storm()
        # Set Sampler
        ct, data = self.encode_multipart_formdata([("pmc","storm"),("sampler","ratfunc"),("sat","z3")], [])
        response = self._sendData('/environment', data, ct)

        # Set auto generator
        ct, data = self.encode_multipart_formdata([("iterations", "2"), ("generator", "uniform")], [])
        response = self._sendData("/generateSamples", data, ct)

        assert response.code == 200

        ct, data = self.encode_multipart_formdata([("iterations", "1"), ("generator", "linear")], [])
        response = self._sendData("/generateSamples", data, ct)

        assert response.code == 200

        ct, data = self.encode_multipart_formdata([("iterations", "1"), ("generator", "delaunay")], [])
        response = self._sendData("/generateSamples", data, ct)

        assert response.code == 200

    def test_auto_constraint(self):
        pass

    def test_constraints(self):
        self.test_run_with_storm()
        ct, data = self.encode_multipart_formdata([("pmc","storm"),("sampler","ratfunc"),("sat","z3")], [])
        response = self._sendData('/environment', data, ct)
        constraint = '[["0.25","0.25"],["0.25","0.50"],["0.50","0.25"],["0.50","0.50"]]'
        ct, data = self.encode_multipart_formdata([("constr-mode", "safe"), ("coordinates", constraint)],[])
        response = self._sendData('/regions', data, ct)
        assert response.code == 200
        pass

    def _get_response_string(self, url):
        """ Returns the value of the json data element as a string. """
        response = self.fetch(url, method='GET', headers=self.header_send)
        s = response.body.decode('UTF-8')
        return json.loads(s)['data']

    def _get_response_code(self, url):
        """ Returns the HTTP response code. """
        response = self.fetch(url, method='GET', headers=self.header_send)
        return response.code

    def _sendData(self, url, data, ct=None):
        headers = dict(self.header_send)
        if ct is not None:
            headers['Content-Type'] = ct
        return self.fetch(url, method='POST', headers=headers, body=data)

    def encode_multipart_formdata(self, fields, files):
        """
        fields is a sequence of (name, value) elements for regular form fields.
        files is a sequence of (name, filename, value) elements for data to be
        uploaded as files.
        Return (content_type, body) ready for httplib.HTTP instance
        """
        BOUNDARY = '----------ThIs_Is_tHe_bouNdaRY_$'
        CRLF = '\r\n'
        L = []
        for (key, value) in fields:
            L.append('--' + BOUNDARY)
            L.append('Content-Disposition: form-data; name="{}"'.format(key))
            L.append('')
            L.append(value)
        for (key, filename, value) in files:
            L.append('--' + BOUNDARY)
            L.append(
                'Content-Disposition: form-data; name="{}"; filename="{}"'.
                    format(
                        key, filename
                    )
            )
            L.append('Content-Type: text/plain')
            L.append('')
            L.append(value)
        L.append('--' + BOUNDARY + '--')
        L.append('')
        body = CRLF.join(L)
        content_type = 'multipart/form-data; boundary=%s' % BOUNDARY
        return content_type, body
