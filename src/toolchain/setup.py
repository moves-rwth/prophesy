from setuptools import setup, find_packages
from setuptools.command.install import install
from setuptools.command.develop import develop
from prophesy.write_config import write_initial_config
import os

dependencies = []

class MyInstall(install):
    user_options = install.user_options + [
        ('customoption=', None, 'Path to something')
    ]

    def initialize_options(self):
        install.initialize_options(self)
        self.customoption = None

    def finalize_options(self):
        print('The custom option for install is ', self.customoption)
        install.finalize_options(self)

    def run(self):
        print("run")
        global mycustomoption
        mycustomoption = self.customoption
        dependencies = ['tornado', 'pycket', 'sympy', 'shapely', 'numpy', 'matplotlib']
        install.run(self)

class MyDevelop(develop):
    user_options = develop.user_options + [
        ('customoption=', None, 'Path to something')
    ]

    def initialize_options(self):
        develop.initialize_options(self)
        self.customoption = None

    def finalize_options(self):
        print('The custom option for install is ', self.customoption)
        develop.finalize_options(self)

    def run(self):
        print("run")
        global mycustomoption
        mycustomoption = self.customoption
        dependencies = ['tornado', 'pycket', 'sympy', 'shapely', 'numpy', 'matplotlib']
        develop.run(self)


def do_setup():

    write_initial_config(os.path.join(os.path.dirname(os.path.realpath(__file__)), "prophesy/prophesy.cfg"))

    setup(cmdclass={'install': MyInstall, 'develop': MyDevelop},
        name="Prophesy",
        version="1.1",
        description="Prophesy - Parametric Probabilistic Model Checking",
        packages=find_packages(),
        install_requires=dependencies,
        package_data={'prophesy': ['prophesy.cfg']}
        )

if __name__ == "__main__":
      do_setup()
