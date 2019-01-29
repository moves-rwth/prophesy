Prophesy
========

Prophesy is a tool set for parameter synthesis of parametric Markov models.
It can work with a variety of backends.
The release of Prophesy is accompanied by an [overview paper]().
To get started, see the notes further below.

Please notice that prophesy is academic software, and mostly meant as a sandbox for developing new algorithms.
Prophesy is licensed under the GPL License. If you are interested in other licensing options, do not hesitate to contact us!

Installation
------------

We advise users to follow [this guide](https://moves-rwth.github.io/prophesy/installation.html). The following outline is very brief.
Make sure you have [carl](http://smtrat.github.io/carl/) in the c++14 version installed.
 
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

Authors
-------

Prophesy is mainly developed at RWTH Aachen University by:

- Sebastian Junges
- Matthias Volk

Prophesy received notable contributions from:

- Harold Bruintjes
- Tom Janson
- Lutz Klinkenberg

We would like to thank Christian Hensel and Tim Quatmann for their contributions in the Storm backend, 
Murat Cubuktepe for his support in developing the QCQP-driven sampling,
and Gereon Kremer for his support of CArL.
Prophesy is developed in close cooperation with Nils Jansen, Joost-Pieter Katoen, and Erika Abraham.
