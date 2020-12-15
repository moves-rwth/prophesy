Installation
=====================

We provide a general introduction into setting up prophesy. If you want to get started as quick as possible, try our step-by-step guides (:ref:`minimal <installation_step_by_step_minimal>` and :ref:`full <installation_step_by_step_full>`)!

Requirements
---------------------
For the base functionality of prophesy, we require Python3 and the latest version of `pycarl <https://moves-rwth.github.io/pycarl/>`_ (including the parser functionality).
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

- Change directories to a suitable location::

    $ cd <location>

- Obtain carl
    * Clone the git repository from `carl <https://github.com/smtrat/carl>`_ with branch `master14`, e.g.::

        $ git clone https://github.com/smtrat/carl.git -b master14
        $ cd carl

    * Prepare the build::

        $ mkdir build && cd build
        $ cmake .. -DUSE_CLN_NUMBERS=ON -DUSE_GINAC=ON

    * Build lib_carl::

        $ make lib_carl

    * Done::

        $ cd <location>

- Obtain carl-parser
    * Clone the git repository from `carl-parser <https://github.com/ths-rwth/carl-parser>`_ with branch `master14`, e.g.::

        $ git clone https://github.com/smtrat/carl-parser.git -b master14
        $ cd carl-parser

    * Prepare the build::

        $ mkdir build && cd build
        $ cmake ..

    * Build the parser::

        $ make

    * Done::

        $ cd <location>

- Obtain pycarl
    * Download the latest release::

        $ git clone https://github.com/moves-rwth/pycarl
        $ cd pycarl

    * Run setup.py, e.g.::

        $ python setup.py develop

    * Done::

        $ cd <location>

- Obtain prophesy
    * Download the latest release

    * Run setup.py and write an initial config file::

        $ python setup.py develop --search-path PATH

      The optional argument defines a search path, where to look for the tools (modelcheckers, SMT solvers, etc.).

    * Done

.. _installation_step_by_step_full:

Step-by-step guide (full)
-------------------------------


- Change directories to a suitable location::

    $ cd <location>

- Obtain carl
    * Clone the git repository from `carl <https://github.com/smtrat/carl>`_ with branch `master14`, e.g.::

        $ git clone https://github.com/smtrat/carl.git -b master14
        $ cd carl

    * Prepare the build::

        $ mkdir build && cd build
        $ cmake .. -DUSE_CLN_NUMBERS=ON -DUSE_GINAC=ON

    * Build lib_carl::

        $ make lib_carl

    * Done::

        $ cd <location>

- Obtain carl-parser
    * Clone the git repository from `carl-parser <https://github.com/ths-rwth/carl-parser>`_ with branch `master14`, e.g.::

        $ git clone https://github.com/smtrat/carl-parser.git -b master14
        $ cd carl-parser

    * Prepare the build::

        $ mkdir build && cd build
        $ cmake ..

    * Build the parser::

        $ make

    * Done::

        $ cd <location>

- Obtain pycarl
    * Download the latest release::

        $ git clone https://github.com/moves-rwth/pycarl
        $ cd pycarl

    * Run setup.py, e.g.::

        $ python setup.py develop

    * Done::

        $ cd <location>

- Obtain storm
    * See the `Storm documentation <https://www.stormchecker.org/documentation/obtain-storm/build.html>`_

- Obtain stormpy
    * See the `Stormpy documentation <https://moves-rwth.github.io/stormpy/installation.html>`_

- Obtain prophesy
    * Download the latest release

    * Run setup.py and write an initial config file::

        $ python setup.py develop --search-path PATH

      The optional argument defines a search path, where to look for the tools (modelcheckers, SMT solvers, etc.).

    * Done
