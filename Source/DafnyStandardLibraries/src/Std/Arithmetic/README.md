# Overview

Non-linear math is generally undecidable; hence Dafny (and Z3) rely on heuristics to prove such properties.
While wonderful when they work, these heuristics can lead to brittle proofs.  Hence, in many projects,
it can be helpful to turn off these heuristics (via Dafny's `--disable-nonlinear-arithmetic` flag) and instead explicitly
invoke the lemmas in this library.  All files in this portion of the library (except those in `Internals/*Nonlinear.dfy`)
verify with the said flag, which should keep the library itself stable.

At a high level, each module contains the algebraic properties of a particular non-linear operation as lemmas either with explicit arguments or as quantified statements (marked `*Auto`).

In general, it shouldn't be necessary to directly reference anything in `Internals`.
