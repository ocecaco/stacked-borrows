# STACKED BORROWS - ARTIFACT

## Technical Appendix

The technical appendix in `appendix.pdf` contains a complete coherent
description of the Stacked Borrows semantics, as well as the definition of our
key simulation relation that we used for the Coq formalization.

## Coq Formalization

We have given informal proof sketches of optimizations based on Stacked Borrows
in the paper. To further increase confidence in the semantics, we started
formalizing these arguments in Coq. Our simulation framework is nearly done
(taking around 11k lines), and we have carried out the proof of one of the
transformations (example1) on top of that framework. We expect the framework and
the remaining proofs to be done very soon.

## Rust Counterexamples and Miri

You can run the counterexamples from the paper in Rust by clicking the following links, and then selecting "Run".
You can also run them in Miri via "Tools" - "Miri", which will show a Stacked Borrows violation.

* [`example1`](https://play.rust-lang.org/?version=stable&mode=release&edition=2018&gist=18e6931728976779452f0d489f59a71c)
* [`example2`](https://play.rust-lang.org/?version=stable&mode=release&edition=2018&gist=85f368db00a789caa08e2b6960ebaf01)
* [`example2_down`](https://play.rust-lang.org/?version=stable&mode=release&edition=2018&gist=66c928ddf745a779272a73262b921a56)

### How to build

#### Build dependencies (via opam)

The easiest way to install the correct versions of the dependencies is through
opam (1.2.2 or newer).  You will need the Coq and Iris opam repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

If opam fails, it is very likely that the required packages were not found.
Run `opam update` to update your opam package registry.

#### Build dependencies (manual installation)

Otherwise, you need to build and install the following dependencies yourself.
See the [opam](opam) file for the exact versions you need.
- Iris
- Paco
- Equations

#### Build

Once the dependencies are installed, you can `make -jN` the development,
replacing `N` by the number of your CPU cores.

### What to look for

The directory structure is as follows:
* `theories/lang`: Definition of the language, including the formalization of
  Stacked Borrows itself in `lang/bor_semantics.v`.
* `theories/sim`: The simulation framework and its adequacy proofs.
* `theories/opt`: Proofs of optimizations. Everything except for `ex1.v` is a
  stub.

The actual proof of the example is in `theories/opt/ex1.v`.  The logical
relation to establish the reflexivity of our simulation relation for well-formed
programs is in `theories/sim/refl.v`.

### Gaps in the proof

The formalization is not entirely finished: our notion of well-formed
expressions (`expr_wf`, a precondition for the reflexivity theorem) excludes not just
programs containing literal locations and administrative instructions (which is
standard), it also excludes deallocation and retagging.

We also have one admitted lemma that gets used in the example proof:
`sim_body_retag_local_mut_ref`, a proof rule for retagging.
