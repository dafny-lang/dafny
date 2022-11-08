# File I/O tests

These files test the basic file I/O facilities in the Dafny runtime.
Currently, there are two file I/O facilities:
one to read all bytes from a file,
and one to write a sequence of bytes to a file.

These are defined as runtime functions/methods named with an "INTERNAL_" prefix,
in order to indicate that users should not depend directly on them.
Instead, users should access the facilities via wrapping modules:
these are the abstract module `AbstractFileIO` and the concrete `FileIO_*` modules
(each named according to the target language).
The `AbstractReadBytesFromFile.dfy` and `ReadBytesFromFile.*.dfy` files demonstrate intended usage
(as do the `AbstractWriteBytesToFile.dfy` and `WriteBytesToFile.*.dfy` files).

TODO:
Once the runtime changes are merged,
the wrapping modules are to be copied into [the libraries repository](https://github.com/dafny-lang/libraries)
for usage in external Dafny code.

## Caveats

* The file to read from (or write to) is specified by a path that is handled by each target language's native file I/O utilities;
  paths are not guaranteed to work identically between target languages.

## Target language support

The file I/O facilities are implemented in these runtimes:

* C#/.NET
* Java
* Javascript
* Python

Support for Golang is planned, but is blocked by <https://github.com/dafny-lang/dafny/issues/2989>.
