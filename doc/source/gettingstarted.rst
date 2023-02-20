
***********************************
A Quick Tour Through Prophesy
***********************************

This tour focuses on the use of the Command Line Interface (CLI).
While the tour is organised around a series of problems common in parameter synthesis,
we recommend first-time users to follow the guide in a linear fashion.

Sampling
=================================

A parametric model can be instantiated with different values for the parameters (instantiations).
Sampling explores the parameter space (i.e. the set of all instantiations) by evaluating various instantiated models

.. code-block:: console

    python scripts/parameter_synthesis.py load-problem model.pm property.pctl sample




The solution function problem
=================================

This problem asks for a closed-form representation that shows how the measure-of-interest
(e.g., the probability to reach a predefined set of target states) depends on the parameter values.
Many probabilistic model checkers support these computations: Prophesy can be used as a uniform gateway to these model checkers

.. code-block:: console

    python scripts/parameter_synthesis.py load-problem model.pm property.pctl compute-solution-function

This tells the CLI to load the problem instance described by the model file and the property file, and then to compute a solution function.
The call can be adapted in several directions

.. code-block:: console

    python scripts/parameter_synthesis.py --mc storm load-problem model.pm property.pctl compute-solution-function --export sol.out

This call has been adapted in two directions: We now specified the model checker to be used, in this case storm, and that the result should be exported to a file sol.out.

The computed solution function can be used to speed up sampling::

    TBD



The exact synthesis problem
=================================

The exact synthesis problem asks for an exact representation of all parameter instantiations that satisfy a specification.
The solution function is a concise (but often very complex) solution.
Prophesy currently does not support any other versions of the exact synthesis problem.


The feasible / optimal instantiation problem
==============================================

The feasible instantiation problem asks for a parameter valuation
such that the induced Markov model satisfies a given property.

There are various approaches to do so:

* SMT
* Particle Swarm Optimisation
* Convex optimisation


Using particle swarm optimisation
---------------------------------

The two essential arguments are whether you want to find a solution above or below the threshold, and what technique to use. Here, we specified to use PSO

.. code-block:: console

    $ python scripts/parameter_synthesis.py load-problem model.pm property.pctl set-threshold 0.1 find-feasible-instantiation below pso

The threshold and the direction in the property should not be specified, i.e., use P=? […] to specify your reachability property.
Instead, we set the threshold to 0.1 by the command line, and then ask prophesy to find a feasible instantiation.

Using convex optimisation
--------------------------------

To switch to convex optimisation, all you need to do is switch the last command to QCQP.
We notice that this method requires gurobi

.. code-block:: console

    $ python scripts/parameter_synthesis.py load-problem model.pm property.pctl set-threshold 0.1 find-feasible-instantiation below qcqp

To speed things up, there are a couple of options that you want to set when using QCQP (they should soon become default flags)

.. code-block:: console

    $ python scripts/parameter_synthesis.py load-problem model.pm property.pctl set-threshold 0.1 find-feasible-instantiation --qcqp-incremental --qcqp-store-quadratic --qcqp-handle-violation minimisation --qcqp-mc full --precheck-welldefinedness below qcqp


Options
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TBD

Using SMT
--------------------------------

TBD

The parameter space partitioning problem
========================================
This problem asks to provide a partitioning into accepting, rejecting and unknown regions, trying to minimize the unknown regions.

.. code-block::

    $  python scripts/parameter_synthesis.py load-problem  examples/smallpmdp/smallpmdp.pm examples/smallpmdp/min.pctl set-threshold 3/10 set-parameter-space --region-string "0.1<=p<=0.2,0.4<=q<=0.6" parameter-space-partitioning --iterations 30 pla quads

This method runs using the quad heuristic for splitting the parameter space,
and uses PLA (parameter lifting) for verifying the regions.

It is often beneficial to sample a bit before running the parameter space partitiong.
We do so by adding the sample command.

.. code-block::

    $  python scripts/parameter_synthesis.py load-problem  examples/smallpmdp/smallpmdp.pm examples/smallpmdp/min.pctl set-threshold 3/10 set-parameter-space --region-string "0.1<=p<=0.2,0.4<=q<=0.6" sample --iterations 2 parameter-space-partitioning --iterations 30 pla quads
