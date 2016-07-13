import os

from prophesy.util import Configuration

class WebConfig(Configuration):
    # Sections
    DIRECTORIES = "directories"

    def __init__(self):
        super().__init__(os.path.join(os.path.dirname(
            os.path.realpath(__file__)), "prophesy_web.cfg"))

    def get_results_dir(self):
        return self.get(WebConfig.DIRECTORIES, "web_results")

    def get_sessions_dir(self):
        return self.get(WebConfig.DIRECTORIES, "web_sessions")

    def get_examples_dir(self):
        return self.get(WebConfig.DIRECTORIES, "web_examples")

configuration = WebConfig()

TOOLNAME = "prophesy_web"
VERSION = [0, 0, 1]
SUPPORT = ["Nils Jansen, Sebastian Junges, Matthias Volk"]
