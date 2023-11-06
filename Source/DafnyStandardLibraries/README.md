# Dafny Standard Libraries

This project contains the source for the standard libraries
that are packaged together with the Dafny distribution.
The libraries in this directory are available automatically 
when you provide the `--standard-libraries` option.
No need to `include` any files! For example:

<!-- %check-verify -->
```dafny
module UsesWrappers {

  import opened DafnyStdLibs.Wrappers

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
We do not yet provide any separately-compiled artifacts with this code.

Because the standard libraries are already pre-verified, `--standard-libraries` is not compatible with all options,
since mixing and matching some options that affect verification across different components is not always safe.
In particular, `--standard-libraries` currently cannot be used together with `--unicode-char:false`.

## Available libraries

The sections below describe how to use each library:

- [DafnyStdLibs.BoundedInts](src/DafnyStdLibs/BoundedInts) -- definitions of types and constants for fixed-bit-width integers
- [DafnyStdLibs.Wrappers](src/DafnyStdLibs/Wrappers) -- simple datatypes to support common patterns, such as optional values or the result of operations that can fail
- [DafnyStdLibs.Relations](src/DafnyStdLibs/Relations) -- properties of relations
- [DafnyStdLibs.Functions](src/DafnyStdLibs/Functions) -- properties of functions

We are in the process of importing many more libraries,
in particular from the existing [`dafny-lang/libraries`](https://github.com/dafny-lang/libraries) GitHub repository.
Stay tuned!

## Backwards compatibility

Because these libraries are packaged together with a specific version of Dafny,
they are not versioned themselves, and instead are updated to continue to work as Dafny itself changes.
Intentional breaking changes will be minimized and accompanied by clear and direct migration instructions.

## Contributing to the libraries

See [CONTRIBUTING.md](CONTRIBUTING.md).
