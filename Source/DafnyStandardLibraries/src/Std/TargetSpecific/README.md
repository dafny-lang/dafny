# File I/O

The `FileIO` module provides basic file I/O operations.
Right now, these are limited to reading bytes from a file, and writing bytes to a file.
The API is intentionally limited in scope and will be expanded later.

The `examples/FileIO` directory contains more detailed examples of how to use the `FileIO` module.

Note that because this module is implemented with target-language utilities,
it is only defined for a subset of the Dafny backends:
currently C#, Java, JavaScript, Go and Python.
For other backends, the `FileIO` module is simply not defined,
so attempting to compile code that uses it to them will result
in resolution errors.
