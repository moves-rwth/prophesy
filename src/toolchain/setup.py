from setuptools import setup, find_packages
import importlib
from prophesy.write_config import write_initial_config
import os

def package_installed(package):
    spec = importlib.util.find_spec(package)
    return spec is not None

def do_setup():
    write_initial_config(os.path.join(os.path.dirname(os.path.realpath(__file__)), "prophesy/prophesy.cfg"))

    setup(
        name="Prophesy",
        version="1.1",
        description="Prophesy - Parametric Probabilistic Model Checking",
        packages=find_packages(),
        install_requires=['tornado', 'pycket', 'sympy', 'shapely', 'numpy', 'matplotlib'],
        extras_require = {
            'carl': ["pycarl"],
            'stormpy' : ["stormpy"]
        },
        package_data={'prophesy': ['prophesy.cfg']}
    )

    print("Found pycarl: ", package_installed("pycarl"))

if __name__ == "__main__":
      do_setup()
