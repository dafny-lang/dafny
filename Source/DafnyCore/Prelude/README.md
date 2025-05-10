## Description

You can extract Dafny model into set of Boogie
declarations. This new feature can be of general use, but its main
application is to justify various axioms in Dafny's `DafnyPrelude.bpl`
by providing a model for them.

## Example: Sequences

The model for Dafny's underlying type `Seq` is given in
`Source/DafnyCore/Prelude/Sequences.dfy`.

The file `../../DafnyCore/DafnyPrelude.bpl` should no longer be edited
by hand. Instead, it is now generated from
`PreludeCore.bpl` and from models such as `Sequences.dfy`.
multisets).

To generate a new version of `DafnyPrelude.bpl`, run `make` in this folder.
This will generate and copy the generated
`../Prelude/Output/DafnyPrelude.bpl` to `../DafnyPrelude.bpl`.

## CLI option

Dafny has a CLI option `--extract:<file>` (where `<file>` is allowed
to be `-` to denote standard output, just like for the various print
options). This option works with the `dafny verify` command.

*Caveats:*

This gets the job done, but is probably not the best way of doing it.
For instance, one could imagine a `dafny extract` command that performs
this task.

## Extract mechanism

Upon successful verification, the new extract mechanism added by this PR
will visit the AST of the given program. For any module marked with
`{:extract}`, the extract-worthy material from the module is output. The
output declarations will be in the same order as they appear textually
in the module (in particular, the fact that module-level Dafny
declarations are collected in an internal class `_default` has no
bearing on the output order).

Three kinds of declarations are extract-worthy:

* A type declaration `A<X, Y, Z>` that bears an attribute
`{:extract_name B}` is extracted into a Boogie type declaration `type B
_ _ _;`.

The definition of the type is ignored. (The intended usage for an
extracted type is that the Dafny program give a definition for the type,
which goes to show the existence of such a type.)

* A function declaration `F(x: X, y: Y): Z` that bears an attribute
`{:extract_name G}` is extracted into a Boogie function declaration
`function G(x: X, y: Y): Z;`.

The body of the Dafny function is ignored. (The intended usage for an
extracted function is that the Dafny program give a definition for the
function, which goes to show the existence of such a function.)

* A lemma declaration `L(x: X, y: Y) requires P ensures Q` that bears an
attribute `{:extract_pattern ...}` or an attribute `{:extract_used_by
...}` is extracted into a Boogie `axiom`. The axiom has the basic form
`axiom (forall x: X, y: Y :: P ==> Q);`.

If the lemma has an attribute `{:extract_used_by F}`, then the axiom
will be emitted into the `uses` clause of the Boogie function generated
for Dafny function `F`.

    If the lemma has no in-parameters, the axiom is just `P ==> Q`.

If the lemma has in-parameters, then any attribute `{:extract_pattern E,
F, G}` adds a matching pattern `{ E, F, G }` to the emitted quantifier.
Also, any attribute `{:extract_attribute "name", E, F, G}` adds an
attribute `{:name E, F, G}` to the quantifier.

## Expressions

The pre- and postconditions of extracted lemmas turn into analogous
Boogie expressions, and the types of function/lemma parameters and bound
variables are extracted into analogous Boogie types. The intended usage
of the extract mechanism is that these expressions and types do indeed
have analogous Boogie types.

At this time, only a limited set of expressions and types are supported,
but more can be added in the future.

Any `forall` and `exists` quantifiers in expressions are allowed to use
`:extract_pattern` and `:extract_attribute` attributes, as described
above for lemmas.

Some extracted expressions are simplified. For example, `true && !!P` is
simplified to `P`.

## Soundness

The Dafny program that is used as input for the extraction is treated
like any other Dafny program. The intended usage of the extraction
mechanism is to prove parts of the axiomatization in `DafnyPrelude.bpl`
to be logically consistent. Whether or not the extracted Boogie
declarations meet this goal depends on the given Dafny program. For
example, if the given Dafny program formalizes sequences in terms of
maps and formalizes maps in terms of sequences, then the extraction
probably does not provide guarantees of consistency.
