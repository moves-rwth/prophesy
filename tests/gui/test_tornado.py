
# Imported to start the webservice and check it's functionality
from prophesy.webservice.webcegar import make_app
from tornado.testing import AsyncHTTPTestCase

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

class TestTornado(AsyncHTTPTestCase):
    """ Testing of the tornado web framework. """

    def get_app(self):
        """ Override to return own application. """
        return make_app("localhost")

    # Sets the environment such that we can read the stored session data.
    def setUp(self):
        super().setUp()
        response = self.fetch('/results')
        self.cookies = response.headers["Set-Cookie"]
        self.header_send = {"Host": "localhost:4242",
            "Accept": "*/*",
            "Cookie": self.cookies,
        }

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

    def test_upload_files(self):
        with open("../../benchmarkfiles/pdtmc/brp/brp_16_2.pm", 'r') as pfile:
            prismdata = pfile.read()
        prismfile = ('prism-file', 'brp_16_2.pm', prismdata)
        ct, data = self.encode_multipart_formdata([], [prismfile])
        print(data)
        response = self._sendData('/uploadPrism', data=data, ct=ct)
        assert response.code == 200


    def _get_response_string(self, url):
        """ Returns the value of the json data element as a string. """
        response = self.fetch(url)
        s = response.body.decode('UTF-8')
        return json.loads(s)['data']

    def _get_response_code(self, url):
        """ Returns the HTTP response code. """
        response = self.fetch(url)
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
