prophesy.sampling package
=========================

Sampling is the package to get a rough image of the parameter space by considering single points in the parameter space.


Sampler: How to sample?
-------------------------------------------

The basic interface for sampling is the sampler interface.
Besides sampling on given points, it supports uniform sampling as some samplers might perform better.

prophesy.sampling.sampler module
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. automodule:: prophesy.sampling.sampler
    :members:
    :undoc-members:
    :show-inheritance:

prophesy.sampling.sampler_ratfunc module
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. automodule:: prophesy.sampling.sampler_ratfunc
    :members:
    :undoc-members:
    :show-inheritance:

Sampling via probabilistic model checking
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
One can also sample via probabilistic model checkers, see :ref:`ref_prophesy.modelcheckers.pmc`.



Sampling: Where to sample?
-------------------------------------------

To determine sample points based on the already sampled information, we provide sample generators.


prophesy.sampling.sample_generator module
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. automodule:: prophesy.sampling.sample_generator
    :members:
    :undoc-members:
    :show-inheritance:


prophesy.sampling.sampling_linear module
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. automodule:: prophesy.sampling.sampling_linear
    :members:
    :undoc-members:
    :show-inheritance:

prophesy.sampling.sampling_uniform module
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. automodule:: prophesy.sampling.sampling_uniform
    :members:
    :undoc-members:
    :show-inheritance:



High-level convenience functions
------------------------------------------

.. This part is not really nice yet, so I put it at the end of the docu.

prophesy.sampling.sampling module
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. automodule:: prophesy.sampling.sampling
    :members:
    :undoc-members:
    :show-inheritance:
