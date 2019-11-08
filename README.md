# STACKED BORROWS - ARTIFACT

## Technical Appendix

The technical [appendix] contains a complete coherent
description of the Stacked Borrows semantics, as well as the definition of our
key simulation relation that we used for the Coq formalization.

[appendix]: appendix.pdf

## Rust Counterexamples and Miri

You can run the counterexamples from the paper in Rust by clicking the following links, and then selecting "Run".
You can also run them in Miri via "Tools" - "Miri", which will show a Stacked Borrows violation.

* [`example1`](https://play.rust-lang.org/?version=stable&mode=release&edition=2018&gist=18e6931728976779452f0d489f59a71c)
  (Section 3.4 of the paper)
* [`example2`](https://play.rust-lang.org/?version=stable&mode=release&edition=2018&gist=85f368db00a789caa08e2b6960ebaf01)
  (Section 3.6)
* [`example2_down`](https://play.rust-lang.org/?version=stable&mode=release&edition=2018&gist=66c928ddf745a779272a73262b921a56)
  (Section 4)

## Coq Formalization

We have given informal proof sketches of optimizations based on Stacked Borrows
in the paper. To further increase confidence in the semantics, we formalized
these arguments in Coq (about 14KLOC). We have carried out the proofs of the
transformations mentioned in the paper: `example1`, `example2`, `example2_down`,
`example3_down`; as well as two more variants to complete the picture,
`example1_down` and `example3`.

### HOW TO START

#### Use a VM

A VM that comes with pre-compiled sources is provided, so that you can start the inspection immediately.

* [artifact.ova](artifact.ova) can be imported into VirtualBox.
  Please give it at least 4GB of RAM.
* The username/password are both `artifact`. After logging in with `artifact`,
  please navigate to `~/sources` for the pre-compiled Coq sources.
* The VM is a minimal Debian 10, pre-installed with `coq` and `coqide` 8.9.1.
  If you want to install extra packages, the `root` password is also `artifact`
  (please use `su` as `sudo` is not installed).

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

#### Rebuild
If you do not trust the precompiled results, you can use `make clean` to remove
them and follow the build instructions above to rebuild.

### STRUCTURE

**Please open files from the folder where the `_CoqProject` file is located, so
that your favorite editing environment can make use of the `_CoqProject` file.**

The directory structure is as follows.

* [theories/lang](theories/lang): Definitions and properties of the language.
  - The language syntax is defined in
    [lang/lang_base.v](theories/lang/lang_base.v).
  - The expression and heap semantics is defined in
    [lang/expr_semantics.v](theories/lang/expr_semantics.v).
  - The semantics of Stacked Borrows itself is in
    [lang/bor_semantics.v](theories/lang/bor_semantics.v). The following table
    matches the definitions in the technical [appendix] with the Coq definitions and their [Miri implementation][Implementation].

    | Definitions in [appendix]      | Coq definitions in `bor_semantics.v` | [Implementation] in Miri |
    |--------------------------------|--------------------------------------|--------------------------|
    | `Grants`                       | `grants`                             | `Permission::grants`     |
    | `FindGranting`                 | `find_granting`                      | `Stack::find_granting`   |
    | `FindFirstWIncompat`           | `find_first_write_incompatible`      | `Stack::find_first_write_incompatible` |
    | `Access`                       | `access1`                            | `Stack::access`          |
    | `MemAccessed(_,_,AccessRead)`  | `memory_read`                        | `Stacks::memory_read`    |
    | `MemAccessed(_,_,AccessWrite)` | `memory_written`                     | `Stacks::memory_written` |
    | `Dealloc`                      | `dealloc1`                           | `Stack::dealloc`         |
    | `MemDeallocated`               | `memory_deallocated`                 | `Stacks::memory_deallocated` |
    | `GrantTag`                     | `grant`                              | `Stack::grant`           |
    | `Reborrow`                     | `reborrow`                           | `EvalContextPrivExt::reborrow` |
    | `Retag`                        | `retag`                              | `EvalContextPrivExt::retag_reference` |

  - The complete language is then combined in [lang/lang.v](theories/lang/lang.v).

[Implementation]: https://github.com/rust-lang/miri/blob/d4e4fe71e6a9568f5d081d99f1c621c5a4ddd7db/src/stacked_borrows.rs

* [theories/sim](theories/sim): The simulation framework and its adequacy proofs.
  - The *local* simulation definition, which is the main simulation relation we
    use to prove optimizations, is in [sim/local.v](theories/sim/local.v).
  - It is then lifted up to the *global* simulation definition in
    [sim/global.v](theories/sim/global.v).
  - Adequacy, which states that the simulation implies behavior inclusion, is in
    [sim/local_adequacy.v](theories/sim/local_adequacy.v),
    [sim/global_adequacy.v](theories/sim/global_adequacy.v),
    [sim/program.v](theories/sim/program.v).
  - Properties of the local simulation with respect to the operational semantics
    are proven in [sim/body.v](theories/sim/body.v),
    [sim/refl_pure_step.v](theories/sim/refl_pure_step.v),
    [sim/refl_mem_step.v](theories/sim/refl_mem_step.v),
    [sim/left_step.v](theories/sim/left_step.v),
    [sim/right_step.v](theories/sim/right_step.v).
  - The main invariant needed for these properties is defined in
    [sim/invariant.v](theories/sim/invariant.v). The invariant is properly
    type-setted in Section 2 of the technical [appendix].
  - In [sim/simple.v](theories/sim/simple.v), we define an easier-to-use but
    less powerful derived simulation relation.
  - The fundamental property that the simulation is reflexive for well-formed
    terms is proven in [sim/refl.v](theories/sim/refl.v).

* [theories/opt](theories/opt): Proofs of optimizations.

    For example, [opt/ex1.v](theories/opt/ex1.v) provides the proof that the
    optimized program refines the behavior of the unoptimized program, where the
    optimized program simply replaces the unoptimized one's `ex1_unopt` function
    with the `ex1_opt` function.

    For this proof, we need to show that (1) `ex1_opt` refines `ex1_unopt`, and
    (2) all other unchanged functions refine themselves.
    The proof of (1) is in the Lemma `ex1_sim_fun`.
    The proof of (2) is the reflexivity of our simulation relation for
    well-formed programs, provided in [theories/sim/refl.v](theories/sim/refl.v).

  - For `example1` (Section 3.4 in the paper),
    see [opt/ex1.v](theories/opt/ex1.v) ;
    `example1_down` did not appear in the paper but we verified it in
    [opt/ex1_down.v](theories/opt/ex1_down.v).
  - For `example2` (Section 3.6) and `example2_down` (Section 4),
    see [opt/ex2.v](theories/opt/ex2.v) and
    [opt/ex2_down.v](theories/opt/ex2_down.v), respectively.
  - For `example3_down` (Section 4),
    see [opt/ex3_down.v](theories/opt/ex3_down.v) ;
    `example3` did not appear in the paper but we verified it in
    [opt/ex3.v](theories/opt/ex3.v).


### SIMULATION FRAMEWORK
The simulation framework developed in this project is a standard simulation via coinduction, and is in fact a simplified version of [Hur et al.'s POPL'12 work](https://doi.org/10.1145/2103621.2103666).
In that sense it is not novel.
The only difference is that our framework depends on the *Iris* Coq library.
However, note that this kind of simulation proofs has not been done in
Iris before, and here we in fact do **not** use the Iris logic to build our simulation.
We only depend on the Iris Coq library for its *resource
algebras* in order to obtain some modularity in our reasoning.

#### Behaviors/Observations
Since we formalize the Stacked Borrows semantics with a rather limited language without external observations (for
example, without `syscall`'s), a program in our language only has the
following observable behaviors:
1. The program gets *stuck* (undefined behavior) after a finite number of steps.
2. The program terminates to a value after finite number of steps.
3. The program diverges with infinite number of silent steps ($\tau$-steps).

The definition `behave_` (in [sim/behavior.v](theories/sim/behavior.v)) lists these cases, and
then we take the greatest fixpoint of `behave_` (a co-induction definition) as
`behave`, using the [paco] library.
The greatest fixpoint is taken so that when the program diverges, its observation actually
has infinite number of steps.
This can be seen in the definition of `behmatch`, where we only make a
corecursive call of `behave` in the `inftau` case.

The theorem `sim_prog_sim_classical` (in [sim/program.v](theories/sim/program.v)) proves that,
if the program `prog_src` simulates `prog_tgt`, i.e. every function of `prog_src`
is in the simulation relation with the corresponding function of `prog_tgt`
(where "corresponding" means they have the same function id in both programs),
then the possible behaviors of `prog_tgt` are *included* in the possible
behaviors of `prog_src`.
As undefined behavior subsumes any behavior, `sim_prog_sim_classical` states
that if `prog_src` does not get stuck (no undefined behavior), then any
observation of `prog_tgt` is also an observation of `prog_src`.
More specifically,
* if `prog_tgt` can terminate to a value, `prog_src` must also be
able to terminate to the same value, and
* if `prog_tgt` can diverge, `prog_src` must also be able to diverge, and
* `prog_tgt` in fact does not get stuck, because that is not an observation of `prog_src`.

#### Simulation relations
The main simulation relation is defined (in the standard way of [paco] proofs) for language expressions in `sim_local_body` (in [sim/local.v](theories/sim/local.v)), and is then lifted to the *function simulation* relation `sim_local_fun`.
The function simulation is then lifted again to the *program simulation* relation (`sim_local_funs`), as defined above in the description of `sim_prog_sim_classical`.

The main simulation relation `sim_local_body` is explained with further comments in
[sim/local.v](theories/sim/local.v).
Every pair of expression `(src,tgt)` in the relation is indexed with a
*pre-condition*, which is some resource *r* (whose type is defined in our
resource algebra *Res*---see Section 2 of the [appendix] for more detail). They
also have a post-condition.
The resource *r* allows us to state abstractly which part of the global state
the pair `(src,tgt)` focuses on.
It is a rely-guarantee setup that allows us to reason locally about functions' bodies, as long as we maintain the invariant on the global state.

#### `FnEntry` or `Default` Retagging?
In the optimization directory ([opt](theories/opt)), one can find different examples, some of which use `FnEntry` retagging, while others use `Default` retagging.
Here, `FnEntry` is used to retag arguments passed into a *Rust* function.
Note that "functions" in our language do **not** always correspond to Rust functions.
Functions in our language can also be used to capture some arbitrary expressions in Rust.
In those cases, when creating new pointers, the `Default` retag is used.

#### Concurrency support
We do not target concurrency at all. This is left for future work.

## Publicly available repositories
===============================

The files contained here were extracted from our [publicly available repository](https://gitlab.mpi-sws.org/FP/stacked-borrows).
The repository is BSD-licensed.

The relevant commit hashes (used when generating the artifact) can be found
in the file [generation_data.txt](generation_data.txt).

[paco]: https://github.com/snu-sf/paco
