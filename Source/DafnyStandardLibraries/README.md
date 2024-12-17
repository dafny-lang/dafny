# Dafny Standard Libraries

This project contains the source for the standard libraries
that are packaged together with the Dafny distribution.
The libraries in this directory are available automatically
when you provide the `--standard-libraries` option.
No need to `include` any files! For example:

<!-- %check-verify -->
```dafny
module UsesWrappers {

  import opened Std.Wrappers

  function SafeDiv(a: int, b: int): Option<int> {
    if b == 0 then None else Some(a/b)
  }

  method Main() {
    print SafeDiv(4, 2), "\n";
    print SafeDiv(7, 0), "\n";
  }
}
```

These libraries are verified ahead of time before adding them to the Dafny tooling,
so switching on this option by itself does not incur any additional verification burden for your Dafny code.

When using this option with commands like `dafny translate`, `dafny build`, or `dafny run`,
the contents of the standard libraries will be automatically included in the translated source code as well. 
This causes conflicts when multiple such translated projects are combined. When combining such projects, please ensure that only one of them has `--translate-standard-library` set to true. 

To combine multiple Dafny projects that were separately built, and were  

Some libraries are dependent on target language utilities, such as `FileIO`.
When `--standard-libraries` is on,
the translation process will also include some additional supporting target language source files,
just as the runtime source is emitted unless `--include-runtime` is off.
These libraries may not be available for all supported languages,
and are simply not defined when translating to those languages.

Because the standard libraries are already pre-verified, `--standard-libraries` is not compatible with all options,
since mixing and matching some options that affect verification across different components is not always safe.
In particular, `--standard-libraries` currently cannot be used together with `--unicode-char:false`.

## Available libraries

The sections below describe how to use each library:

- [Std.Arithmetic](src/Std/Arithmetic/README.md) -- utilities and lemmas related to basic operations, such as multiplication and exponentiation
- [Std.Base64](src/Std/Base64.md) -- base-64 encoding and decoding
- [Std.BoundedInts](src/Std/BoundedInts.md) -- definitions of types and constants for fixed-bit-width integers
- [Std.Collections](src/Std/Collections/Collections.md) -- properties of the built-in collection types (seq, set, iset, map, imap, array)
- [Std.Concurrent](src/Std/TargetSpecific) -- types for using Dafny in concurrent environments
- [Std.DynamicArray](src/Std/DynamicArray.dfy) -- an array that can grow and shrink
- [Std.FileIO](src/Std/TargetSpecific) -- basic file I/O operations
- [Std.Functions](src/Std/Functions.md) -- properties of functions
- [Std.JSON](src/Std/JSON/JSON.md) -- JSON serialization and deserialization
- [Std.Math](src/Std/Math.md) -- common mathematical functions, such as Min and Abs
- [Std.Relations](src/Std/Relations.md) -- properties of relations
- [Std.Strings](src/Std/Strings.md) -- utilities for strings, especially converting to and from string representations of common types
- [Std.Unicode](src/Std/Unicode/Unicode.md) -- implementations of basic algorithms from Unicode 15.0
- [Std.Wrappers](src/Std/Wrappers.md) -- simple datatypes to support common patterns, such as optional values or the result of operations that can fail

## Backwards compatibility

Because these libraries are packaged together with a specific version of Dafny,
they are not versioned themselves, and instead are updated to continue to work as Dafny itself changes.
Intentional breaking changes will be minimized and accompanied by clear and direct migration instructions.

## Contributing to the libraries

See [CONTRIBUTING.md](CONTRIBUTING.md).
