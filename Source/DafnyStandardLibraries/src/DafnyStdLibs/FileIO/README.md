# File I/O

The `FileIO` module provides basic file I/O operations.
Right now, these are limited to reading bytes from a file, and writing bytes to a file.
The API is intentionally limited in scope and will be expanded later.

Unlike other modules in the `libraries` repo,
the `FileIO` module will not compile or run correctly without a language-specific implementation file.
Language-specific implementation files are provided for C#/.NET, Java, and Javascript.
(Python and Golang support are planned.)
Concretely, to use `FileIO` in your code, you must:

1. `include` and `import` the `FileIO` module as you would any other library module
2. incorporate the corresponding language-specific implementation file (e.g. `FileIO.cs`) when building or running your program

For example, to run a `Program.dfy` file that depends on the `FileIO` module, run the following.
(This assumes you have the `libraries` repository checked out within the working directory.)

```bash
# C#/.NET
$ dafny run Program.dfy --input libraries/src/FileIO/FileIO.cs

# Java
$ dafny run Program.dfy --target:java --input libraries/src/FileIO/FileIO.java

# Javascript
$ dafny run Program.dfy --target:js --input libraries/src/FileIO/FileIO.js
```

(If you aren't using `dafny run` to run your program,
then you should instead integrate the appropriate language-specific implementation file in your build system.)

The `examples/FileIO` directory contains more detailed examples of how to use the `FileIO` module.
