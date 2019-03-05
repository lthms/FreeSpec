.. FreeSpec documentation master file, created by
   sphinx-quickstart on Fri Feb  8 13:47:28 2019.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

Welcome to FreeSpec's documentation!
====================================

FreeSpec is a *compositional reasoning* framework for the Coq proof
assistant. It allows for building up a complex system by connecting components
together through well defined *interfaces*. It also allows for reasoning about
the correctness about the system, thanks to so-called *abstract
specification*. Components are verified in isolation, following by their
*composition* so that local properties can be extended to the system as a whole.

FreeSpec leverages popular abstractions in programming language communities.
Components are primilarly identified by the *interface* (the set of operations)
they expose for other components to use, and secondarily by the interfaces they
use. Then, components are modeled as “program of effects” of the interfaces they
use, and can act as “effects handler” for the interface they expose.

The present manual presents the key concepts of FreeSpec, and its various
extensions.

.. toctree::
   :maxdepth: 2
   :caption: Contents

   core

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
