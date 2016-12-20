from distutils.core import setup
from setuptools.command.test import test as TestCommand
import os
import sys

if sys.version_info[0] == 2:
    sys.exit("Sorry, Python 2 is not supported.")

class Tox(TestCommand):
    """Custom command to execute the tests using tox
    """

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
    # Write config before executing setup, so cfg files are found
    os.system('python write_config.py')

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
            'prophesy_web': ['prophesy_web.cfg', 'static/*.*', 'static/flot/*']
        },
        scripts=['scripts/buildconstraints',
                 'scripts/prismfilesampling',
                 'scripts/prismfiletoratfunc',
                 'scripts/ratfilesampling',
                 'scripts/webcegar'],
        cmdclass={
          'test': Tox
        }
    )

if __name__ == "__main__":
    do_setup()
