from distutils.core import setup
from distutils.command.build import build
from setuptools.command.test import test as TestCommand
import write_config
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

class ConfigBuild(build):

    def run(self):
        # Write config before executing setup, so cfg files are found
        write_config.write_initial_config()
        build.run(self) 

setup(
    name="Prophesy",
    version="1.2",
    author="S. Junges, H. Bruintjes, M. Volk",
    author_email="sebastian.junges@cs.rwth-aachen.de",
    maintainer="S. Junges",
    maintainer_email="sebastian.junges@cs.rwth-aachen.de",
    url="http://moves.rwth-aachen.de",
    description="Prophesy - Parametric Probabilistic Model Checking",
    packages=["prophesy", "prophesy.smt",
              "prophesy.sampling", "prophesy.output", "prophesy.input",
              "prophesy.modelcheckers", "prophesy.data",
              "prophesy.regions", "prophesy.exceptions",
              "prophesy_web"],
    install_requires=['tornado', 'pycket', 'redis', 'pycarl>=2.0', 'stormpy', 'shapely',
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
    scripts=['scripts/buildconstraints.py',
             'scripts/modelsampling.py',
             'scripts/prismfiletoratfunc.py',
             'scripts/ratfilesampling.py',
             'scripts/webcegar'],
    cmdclass={
        'build': ConfigBuild,
        'test': Tox
    }
)
