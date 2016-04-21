from prophesy.webservice.webcegar import make_app

from tornado.testing import AsyncHTTPTestCase
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
        self.header_send = {"Host": "localhost:4242",
            "Accept": "*/*",
            "Cookie": self.cookies,
        }

    def test_homepage(self):
        """ Test the prophesy homepage. """
        response = self.fetch('/')
        self.assertEqual(response.code, 200)
    
    def test_config(self):
        """ Test the configuration. """
        
        # Create random new test value
        new_value = str(random.random())
        response = self.fetch('/config/test/test_value')
        s = response.body.decode('UTF-8')
        value_before = json.loads(s)["data"]
        while new_value == value_before:       
            new_value = str(random.random())
 
        # Change value
        body_send = "data=" + new_value
        response = self.fetch('/config/test/test_value', method='POST', headers=self.header_send, body=body_send)
        self.assertEqual(response.code, 200)
        s = response.body.decode('UTF-8')
        
        # Check new value
        response = self.fetch('/config/test/test_value')
        s = response.body.decode('UTF-8')
        value_after = json.loads(s)["data"]
        self.assertNotEqual(value_before, value_after)
        self.assertEqual(value_after, new_value)

