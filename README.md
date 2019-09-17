# STACKED BORROWS - ARTIFACT

## Technical Appendix

The technical appendix in `appendix.pdf` contains a complete coherent
description of the Stacked Borrows semantics, as well as the definition of our
key simulation relation that we used for the Coq formalization.

## Rust Counterexamples and Miri

You can run the counterexamples from the paper in Rust by clicking the following links, and then selecting "Run".
You can also run them in Miri via "Tools" - "Miri", which will show a Stacked Borrows violation.

* [`example1`](https://play.rust-lang.org/?version=stable&mode=release&edition=2018&gist=18e6931728976779452f0d489f59a71c)
* [`example2`](https://play.rust-lang.org/?version=stable&mode=release&edition=2018&gist=85f368db00a789caa08e2b6960ebaf01)
* [`example2_down`](https://play.rust-lang.org/?version=stable&mode=release&edition=2018&gist=66c928ddf745a779272a73262b921a56)

## Coq Formalization

We have given informal proof sketches of optimizations based on Stacked Borrows
in the paper. To further increase confidence in the semantics, we formalized
these arguments in Coq (about 14KLOC). We have carried out the proofs of the
transformations mentioned in the paper: `example1`, `example2`, `example2_down`,
`example3_down`; as well as two more variants to complete the picture,
`example1_down` and `example3`.

### What to look for

The directory structure is as follows:
* `theories/lang`: Definitions and properties of the language.
  - The language syntax is defined in `lang/lang_base.v`.
  - The expression and heap semantics is defined in `lang/expr_semantics.v`.
  - The semantics of Stacked Borrows itself is in `lang/bor_semantics.v`.
  - The complete language is then combined in `lang/lang.v`.
* `theories/sim`: The simulation framework and its adequacy proofs.
  - The local simulation definition is in `sim/local.v`.
  - It is then lifted up to the global simulation definition in `sim/global.v`.
  - Adequacy (that the simulation implies behavior inclusion) is in `sim/local_adequacy.v`, `sim/global_adequacy.v`, and `sim/program.v`.
  - Properties of the simulation with respect to the operational semantics are
  proven in `sim/body.v`, `sim/refl_pure_step.v`, `sim/refl_mem_step.v`,
  `sim/left_step.v`, `sim/right_step.v`.
  - The main invariant needed for these properties is defined in `sim/invariant.v`.
  - In `sim/simple.v`, we define an easier-to-use but less powerful derived simulation relation.
  - The fundamental property that the simulation is reflexive for well-formed terms is proven in `sim/refl.v`.
* `theories/opt`: Proofs of optimizations.

    For example, `theories/opt/ex1.v` provides the proof that the optimized
    program refines the behavior of the unoptimized program, where the optimized
    program simply replaces the unoptimized one's `ex1_unopt` function the
    `ex1_opt` function.

    For this proof, we need to show that (1) `ex1_opt` refines `ex1_unopt`, and (2) all other unchanged functions refine themselves.
    The proof of (1) is in the Lemma `ex1_sim_fun`.
    The proof of (2) is the reflexivity of our simulation relation for well-formed programs, provided in `theories/sim/refl.v`.

  - For `example1` (Section 3.4 in the paper), see `opt/ex1.v`; `example1_down` did not appear in the paper but we verified it in `opt/ex1_down.v`.
  - For `example2` (Section 3.6) and `example2_down` (Section 4), see `opt/ex2.v` and `opt/ex2_down.v`, respectively.
  - For `example3_down` (Section 4), see `opt/ex3_down.v`; `example3` did not appear in the paper but we verified it in `opt/ex3.v`.


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
