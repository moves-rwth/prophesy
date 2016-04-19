from setuptools import setup, find_packages
from setuptools.command.test import test as TestCommand
from prophesy.write_config import write_initial_config
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


def do_setup():
    setup(
        cmdclass = {'test': Tox},
        name="Prophesy",
        version="1.1",
        description="Prophesy - Parametric Probabilistic Model Checking",
        packages=["prophesy", "prophesy.smt",
                   "prophesy.sampling", "prophesy.output", "prophesy.input", "prophesy.modelcheckers", "prophesy.data", "prophesy.regions", "prophesy.exceptions"],
        install_requires=['tornado', 'pycket', 'redis', 'pycarl', 'shapely', 'numpy', 'matplotlib'],
        tests_require=['pytest'],
        extras_require = {
            'carl': ["pycarl"],
            'stormpy' : ["stormpy"],
            'pdf': ["PyPDF2"],
        },
        package_data={'prophesy': ['prophesy.cfg']}
    )

    write_initial_config(os.path.join(os.path.dirname(os.path.realpath(__file__)), "prophesy/prophesy.cfg"))


if __name__ == "__main__":
      do_setup()
