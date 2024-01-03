Prophesy
========

Prophesy is a tool set for parameter synthesis of parametric Markov models, developed between 2015 and 2019. 
Please notice that prophesy is academic software, and mostly meant as a sandbox for developing new algorithms.
Prophesy is no longer actively developed. 

The so-far final release of Prophesy is accompanied by an [overview paper](https://arxiv.org/pdf/1903.07993.pdf).

Installation
------------

We advise users to follow [this guide](https://moves-rwth.github.io/prophesy/installation.html). 

Then:

    python setup.py develop

installs the required dependencies and prophesy.

It will create `prophesy/prophesy.cfg` and `prophesy/dependencies.cfg` which you might want to extend.

Running:

    python -m pytest tests
    python -m pytest scripts/tests

executes varying tests. Any occurrences of `s` show that your support currently does not contain some optional dependencies.


Getting Started
---------------

The command line tools are available in the `scripts` folder.


Examples
--------
The directory `examples` contains parametric models which can be used as input for Prophesy.
The directory `benchmark_files` contains additional parametric models which have been used as benchmarks in the [overview paper](https://arxiv.org/pdf/1903.07993.pdf).


Authors
-------

Prophesy was mainly developed at RWTH Aachen University by:

- [Sebastian Junges](https://moves.rwth-aachen.de/people/sebastian-junges/)
- [Matthias Volk](https://moves.rwth-aachen.de/people/volk/)

Prophesy received notable contributions from:

- Harold Bruintjes
- Tom Janson
- Lutz Klinkenberg

We would like to thank Christian Hensel and [Tim Quatmann](https://moves.rwth-aachen.de/people/quatmann/) for their contributions in the [Storm](https://www.stormchecker.org) backend,
Murat Cubuktepe for his support in developing the QCQP-driven feasibility sampling,
and Gereon Kremer for his support of CArL.
Prophesy is developed in close cooperation with [Nils Jansen](http://nilsjansen.org), [Joost-Pieter Katoen](http://www-i2.informatik.rwth-aachen.de/~katoen/), and [Erika Abraham](https://ths.rwth-aachen.de/people/erika-abraham/).
