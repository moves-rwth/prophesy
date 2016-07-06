import pytest

# Imported to start the webservice and check it's functionality
from prophesy.webservice.webcegar import make_app, initEnv
from tornado.testing import AsyncHTTPTestCase

# For parsing json-strings in dicts
import json

class TornadoTestCase(AsyncHTTPTestCase):
    """ General class for testing the tornado web framework. """
    app = None

    def get_app(self):
        """ Override to return own application. """
        if self.app is None:
            initEnv()
            self.app = make_app("localhost")
        return self.app

    def setUp(self):
        """ Set the environment such that we can read the stored session data """
        super().setUp()
        response = self.fetch('/results')
        self.cookies = response.headers["Set-Cookie"]
        self.header_send = {"Host": "localhost:4242",
            "Accept": "*/*",
            "Cookie": self.cookies,
        }

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
        """ Send data via POST """
        headers = dict(self.header_send)
        if ct is not None:
            headers['Content-Type'] = ct
        return self.fetch(url, method='POST', headers=headers, body=data)

    def _encode_multipart_formdata(self, fields, files):
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
