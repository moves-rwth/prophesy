from tornado.testing import AsyncHTTPTestCase
from tornado.httpclient import HTTPRequest
import urllib
from prophesy.webservice.webcegar import make_app
import json
import random

class TestTornado(AsyncHTTPTestCase):
    """ Testing of the tornado web framework. """

    def get_app(self):
        """ Override to return own application. """
        return make_app("localhost")

    def setUp(self):
        super().setUp()
        response = self.fetch('/results')
        self.cookies = response.headers["Set-Cookie"]

    def test_homepage(self):
        """ Test the prophesy homepage. """
        response = self.fetch('/')
        self.assertEqual(response.code, 200)
    
    def test_config(self):
        """ Test the configuration. """
        new_value = str(random.random())
        response = self.fetch('/config/test/test_value')
        s = response.body.decode('UTF-8')
        value_before = json.loads(s)["data"]
        while new_value == value_before:       
            new_value = str(random.random())
 
        # Change value
        headers_new = {"Host": "localhost:4242",
            "Accept": "*/*",
            "Content-Type": "application/json",
            "Cookie": self.cookies,
        }
        response = self.fetch('/config/test/test_value?data=' + new_value, method='POST', headers = headers_new, body="")
        self.assertEqual(response.code, 200)
        s = response.body.decode('UTF-8')
        
        # Change new value
        response = self.fetch('/config/test/test_value')
        s = response.body.decode('UTF-8')
        value_after = json.loads(s)["data"]
        self.assertNotEqual(value_before, value_after)
        self.assertEqual(value_after, new_value)

