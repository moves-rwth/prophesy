from setuptools import setup, find_packages
from setuptools.command.test import test as TestCommand
import importlib
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


def package_installed(package):
    spec = importlib.util.find_spec(package)
    return spec is not None

def do_setup():
    write_initial_config(os.path.join(os.path.dirname(os.path.realpath(__file__)), "prophesy/prophesy.cfg"))

    setup(
        cmdclass = {'test': Tox},
        name="Prophesy",
        version="1.1",
        description="Prophesy - Parametric Probabilistic Model Checking",
        packages=find_packages(),
        install_requires=['tornado', 'pycket', 'sympy', 'shapely', 'numpy', 'matplotlib'],
        test_requires=['tox'],
        extras_require = {
            'carl': ["pycarl"],
            'stormpy' : ["stormpy"],
            'pdf': ["PyPDF2"],
        },
        package_data={'prophesy': ['prophesy.cfg']}
    )

    print("Found pycarl: ", package_installed("pycarl"))
    print("Found stormpy: ", package_installed("stormpy"))
    print("Found PyPDF2: ", package_installed("PyPDF2"))

if __name__ == "__main__":
      do_setup()
