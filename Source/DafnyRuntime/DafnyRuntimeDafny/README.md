This project contains implementations of functionalities needed at runtime.
They are intended to be cross-compiled to multiple runtimes
in order to provide a single verified source.
It is currently limited to a moderately-optimized implementation of the `seq<T>` builtin type
as a `Sequence<T>` trait and related classes,
and currently only used to generate this part of the Go runtime.

Because this application depends also on correcting some small Go compiler bugs at the same time,
it's not feasible to use a released Dafny implementation to compile this Dafny code to Go.
Instead we temporarily check in the generated file
and include a test that runs the locally-built Dafny against this Dafny source code
and asserts the output is identical.
Once the needed bugs are released
(and potentially other improvements 
that we'd strongly prefer to have in the bootstrapping Dafny version),
we can delete the generated code from the repository
and generate it during the actual build of the runtimes.

Note also that that our planned bootstrapping strategy at that point
is to pick a released version of Dafny and stick with it as long as possible.
Updating to a newer version implies trusting its implementation,
and building Dafny completely from source will then involve
multiple steps of building older versions from scratch.
We hope to move to [a more sustainable strategy](https://bootstrappable.org/best-practices.html)
before this chain of trust gets too long.
