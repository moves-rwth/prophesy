A Quick Tour Through Prophesy
===============================

This tour focusses on the use of the Command Line Interface (CLI).
While the tour is organised around a series of problems common in parameter synthesis,
we recommend first-time users to follow the guide in a linear fashion.

Sampling
----------------------------------

A parametric model can be instantiated with different values for the parameters (instantiations).
Sampling explores the parameter space (i.e. the set of all instantiations) by evaluating various instantiated models::

    python scripts/parameter_synthesis.py load-problem model.pm property.pctl sample




The solution function problem
----------------------------------

This problem asks for a closed-form representation that shows how the measure-of-interest
(e.g., the probability to reach a predefined set of target states) depends on the parameter values.
Many probabilistic model checkers support these computations: Prophesy can be used as a uniform gateway to these model checkers::

    python scripts/parameter_synthesis.py load-problem model.pm property.pctl compute-solution-function

This tells the CLI to load the problem instance described by the model file and the property file, and then to compute a solution function.
The call can be adapted in several directions::

    python scripts/parameter_synthesis.py --mc storm load-problem model.pm property.pctl compute-solution-function --export sol.out

This call has been adapted in two directions: We now specified the model checker to be used, in this case storm, and that the result should be exported to a file sol.out.

The computed solution function can be used to speed up sampling::

The exact synthesis problem
----------------------------------

The exact synthesis problem asks for an exact representation of all parameter instantiations that satisfy a specification.
The solution function is a concise (but often very complex) solution.
Prophesy currently does not support any other versions of the exact synthesis problem.


The feasible / optimal instantiation problem
----------------------------------

TBD

The approximate synthesis problem
----------------------------------


