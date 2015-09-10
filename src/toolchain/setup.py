from setuptools import setup, find_packages
setup(name="Prophesy",
      version="1.1",
      description="Prophesy - Parametric Probabilistic Model Checking",
      packages=find_packages(),
      install_requires=['tornado', 'pycket', 'sympy', 'shapely', 'numpy'])