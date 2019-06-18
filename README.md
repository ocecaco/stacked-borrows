# BUILD INSTRUCTIONS
The easiest way to install the correct versions of the dependencies is through
opam (1.2.2 or newer).  You will need the Coq and Iris opam repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

Otherwise, you need to install the following dependencies.
See [opam](opam) for the exact versions you need for them.
- A development version of Iris
- Paco
- Equations
