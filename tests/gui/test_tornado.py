from tornado.testing import AsyncHTTPTestCase
from prophesy.webservice.webcegar import make_app

class TestTornado(AsyncHTTPTestCase):
    """ Testing of the tornado web framework. """

    def get_app(self):
        """ Override to return own application. """
        return make_app("localhost")

    def test_homepage(self):
        """ Test the prophesy homepage. """
        response = self.fetch('/')
        self.assertEqual(response.code, 200)
    
    def test_config(self):
        """ Test the configuration. """
        response = self.fetch('/config')
        self.assertEqual(response.code, 200)
        self.assertIn(response.body, "sampling_threshold_new")

