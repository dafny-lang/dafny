# Target-specific Libraries

Note that because these modules are implemented with target-language utilities,
they are only defined for a subset of the Dafny backends:
currently C#, Java, JavaScript, Go and Python.
For other backends, the modules are simply not defined,
so attempting to compile code that uses it will result
in resolution errors.

## File I/O

The `FileIO` module provides basic file I/O operations.
Right now, these are limited to reading bytes from a file, and writing bytes to a file.
The API is intentionally limited in scope and will be expanded later.

The `examples/FileIO` directory contains more detailed examples of how to use the `FileIO` module.

## Concurrent

Dafny has no notion of concurrency, but we supply some tools to support using
generated code in an concurrent environment. 
They allow mutable state to be shared between concurrent executions of Dafny code,
which is particularly useful for caching.

Most of the types in this library do not model their mutable state as part of
Dafny's model of the heap,
since Dafny's model currently assumes only sequential access.
Instead, they model their state as implicit non-determinism.
In other words, rather than defining a `MutableMap.Get` function that `reads this.Repr`,
we define a `MutableMap.Get` method with a non-deterministic result.
This accurately reflects the fact that if one thread `Put`s a value into a `MutableMap`
and then later tries to `Get` it out again,
it may not retrieve the same value because of the interference of other threads.
Therefore all of the interfaces are declared with ONLY methods and no functions,
since functions must be deterministic based on their parameters and the state of the Dafny heap.

These types should be used with caution,
as the verifier is only able to ensure that no unprotected Dafny heap state
is shared between concurrent executions
(see [the `{:concurrent}` attribute](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-concurrent-attribute)).
It cannot currently offer any other guarantees related to concurrent execution,
such as freedom from deadlocks.
