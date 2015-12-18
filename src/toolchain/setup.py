from setuptools import setup, find_packages
from prophesy.write_config import write_initial_config
import os

write_initial_config(os.path.join(os.path.dirname(os.path.realpath(__file__)), "prophesy/prophesy.cfg"))

setup(name="Prophesy",
      version="1.1",
      description="Prophesy - Parametric Probabilistic Model Checking",
      packages=find_packages(),
      install_requires=['tornado', 'pycket', 'sympy', 'shapely', 'numpy', 'matplotlib'],
      extras_require={'fast_rational_sampling': ['pycarl']},
      package_data={'prophesy': ['prophesy.cfg']}
      )
