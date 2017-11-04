from distutils.core import setup
from distutils.command.build import build
from setuptools.command.test import test as TestCommand
import write_config
import sys
import re

if sys.version_info[0] == 2:
    sys.exit("Sorry, Python 2 is not supported.")


def obtain_version():
    """
    Obtains the version as specified in prophesy.
    :return: Version of prophesy.
    """
    verstr = "unknown"
    try:
        verstrline = open('prophesy/_version.py', "rt").read()
    except EnvironmentError:
        pass  # Okay, there is no version file.
    else:
        VSRE = r"^__version__ = ['\"]([^'\"]*)['\"]"
        mo = re.search(VSRE, verstrline, re.M)
        if mo:
            verstr = mo.group(1)
        else:
            raise RuntimeError("unable to find version in prophesy/_version.py")
    return verstr


class Tox(TestCommand):
    """Custom command to execute the tests using tox
    """

    def finalize_options(self):
        TestCommand.finalize_options(self)
        self.test_args = []
        self.test_suite = True

    def run_tests(self):
        # import here, cause outside the eggs aren't loaded
        import tox
        errcode = tox.cmdline(self.test_args)
        sys.exit(errcode)


class ConfigBuild(build):
    user_options = build.user_options + [
        ('search-path=', None, 'Path to search for tools'),
    ]

    def initialize_options(self):
        build.initialize_options(self)
        self.search_path = None

    def finalize_options(self):
        build.finalize_options(self)

    def run(self):
        # Write config before executing setup, so cfg files are found
        write_config.write_initial_config(self.search_path)
        build.run(self)


setup(
    name="Prophesy",
    version=obtain_version(),
    author="S. Junges, H. Bruintjes, M. Volk",
    author_email="sebastian.junges@cs.rwth-aachen.de",
    maintainer="S. Junges",
    maintainer_email="sebastian.junges@cs.rwth-aachen.de",
    url="http://moves.rwth-aachen.de",
    description="Prophesy - Parametric Probabilistic Model Checking",
    packages=["prophesy", "prophesy.smt", "prophesy.sampling", "prophesy.output", "prophesy.input",
              "prophesy.modelcheckers", "prophesy.data", "prophesy.regions", "prophesy.exceptions", "prophesy_web"],
    install_requires=['tornado', 'pycket', 'redis', 'pycarl>=2.0.1', 'shapely',
                      'numpy', 'matplotlib', 'heuristic_optimization>=0.4.3,<0.5', 'click'],
    tests_require=['pytest'],
    extras_require={
        'stormpy': ["stormpy"],
        'pdf': ["PyPDF2"],
    },
    package_data={
        'prophesy': ['prophesy.cfg'],
        'prophesy_web': ['prophesy_web.cfg', 'static/*.*', 'static/flot/*']
    },
    scripts=[
        'scripts/parameter_synthesis.py',
        'scripts/sampling_model.py',
        'scripts/sampling_solutionfunction.py',
        'scripts/parameter_space_partitioning.py',
        'scripts/webcegar.py'],
    cmdclass={
        'build': ConfigBuild,
        'test': Tox
    }
)
