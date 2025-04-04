# The `Termination` module

The `Termination` module includes a `TerminationMetric` datatype
that can represent most `decreases` clauses in Dafny code.
It is useful for more dynamic termination metrics in generic code.
In particular, it is heavily used by the [Actions](Actions/Actions.md) module
to represent a bound on how many more elements a `Producer` may produce,
in order to prove it eventually produces `None`.

`TerminationMetric` values are mapped to `ORDINAL` values via an `Ordinal()` function.
This provides the basis of the well-founded order on `TerminationMetric`,
and also allows them to be used indirectly in `decreases` clauses
as `decreases terminationMetric.Ordinal()`.
In a sense, a `TerminationMetric` provides a convenient way
to hold onto a structured `ORDINAL` value
and invoke lemmas such as `TupleDecreasesToTuple`
in order to prove that one value decreases to another.

The possible values and the relationships between them
are a superset of what Dafny `decreases` clauses are able to express.
For example, the encoding of lexicographical tuples
lets you establish the equivalent of `a, b decreases to b`,
which is not supported in Dafny.
This is still sound because of applying upper bounds on elements as preconditions,
so there are still no infinite descending chains
(proven by the mapping to the ordinals).
