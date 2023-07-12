# DafnyBenchmarkingPlugin

This compiler plugin adds support for a class-level `{:benchmarks}` attribute,
for defining harnesses to measure the performance of Dafny code.
It can also be used to check for concurrent execution bugs
just by verifying the benchmarking process doesn't crash.

For now this plugin only supports the Java backend,
but support for the other languages will be added in the future.

## Example

See [this regression test](../../Test/benchmarks/sequence-race/SequenceRace.dfy) 
for a race condition in the Dafny runtime.