Installation
=====================

We provide a general introduction into setting up prophesy. If you want to get started as quick as possible, try our step-by-step guides (:ref:`minimal <installation_step_by_step_minimal>` and :ref:`full <installation_step_by_step_full>`)!

Requirements
---------------------
For the base functionality of prophesy, we require Python3 and the latest version of `pycarl <https://moves-rwth.github.io/pycarl/>`_.
You can then run the setup.py command with the environment of your choice.

To use the different features of prophesy, we suggest that you at least have
- a probabilistic model checker, e.g. `storm <https://www.stormchecker.org>`_.
- an smt-checker with nonlinear real arithmetic support (QF_NRA), e.g. `z3 <https://github.com/Z3Prover/z3>`_.
It is easiest to first install these or other optional dependencies, and only then install prophesy.
This way, chances are that prophesy will find the tools itself.

To make the most out of prophesy, we suggest that you use `stormpy <https://moves-rwth.github.io/stormpy/>`_, which
are python bindings for the model checker storm. These allow an interactive communication with the model checker backend,
which drastically improves performance of some methods.

.. _installation_step_by_step_minimal:

Step-by-step guide (minimal)
-------------------------------

Test

.. _installation_step_by_step_full:

Step-by-step guide (full)
-------------------------------

Test

