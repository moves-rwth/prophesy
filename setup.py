from distutils.core import setup, Command

from setuptools.command.test import test as TestCommand
from distutils.command.build import build as orig_build
import os
import sys


class Tox(TestCommand):
    def finalize_options(self):
        TestCommand.finalize_options(self)
        self.test_args = []
        self.test_suite = True
    def run_tests(self):
        #import here, cause outside the eggs aren't loaded
        import tox
        errcode = tox.cmdline(self.test_args)
        sys.exit(errcode)

class build(orig_build):
    def run(self):
        self.run_command("build_config")
        orig_build.run(self)

class build_config(Command):
    description = "run initial configuration"
    user_options = []
    def initialize_options(self):
        pass

    def finalize_options(self):
        pass

    def run(self):
        os.system('python write_config.py')

def do_setup():
    setup(
        name="Prophesy",
        version="1.1",
        description="Prophesy - Parametric Probabilistic Model Checking",
        packages=["prophesy", "prophesy.smt",
                  "prophesy.sampling", "prophesy.output", "prophesy.input",
                  "prophesy.modelcheckers", "prophesy.data",
                  "prophesy.regions", "prophesy.exceptions",
                  "prophesy_web"],
        install_requires=['tornado', 'pycket', 'redis', 'pycarl', 'shapely',
                          'numpy', 'matplotlib'],
        tests_require=['pytest'],
        extras_require = {
            'stormpy' : ["stormpy"],
            'pdf': ["PyPDF2"],
        },
        package_data={
            'prophesy': ['prophesy.cfg'],
            'prophesy_web': ['prophesy_web.cfg', 'static']
        },
        cmdclass={
          'build': build,
          'build_config': build_config,
          'test': Tox
        }
    )

if __name__ == "__main__":
    do_setup()
