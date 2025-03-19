# The `Termination` module

The `Termination` module includes a `TerminationMetric` datatype
that can represent most `decreases` clauses in Dafny code.
It is useful for more dynamic termination metrics
in generic code.
In particular, it is heavily used by the [Actions](Actions/Actions.md) module
to represent a bound on how many more elements a `Producer` may produce,
in order to prove it eventually produces `None`.