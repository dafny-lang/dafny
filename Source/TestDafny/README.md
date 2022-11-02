# TestDafny (a.k.a %testdafny)

This internal, testing-only utility is used to execute a single Dafny source file against each compile target option and assert that the output
is the same as the corresponding `<test file>.expect` file. This is a very common testing approach implemented manually across the integration test suite with multiple
lit commands. See [this test file](../../Test/metatests/ConsistentWhenSupported.dfy) for a comparison of the manual approach
compared to using this utility.

Note the manual approach currently used in most test files has several downsides:

1. New compilers have to be manually added to every relevant test file.
2. The expected output must be duplicated for each compile target, making it hard to perceive inconsistencies.
3. When a test fails, it is difficult to determine from the output which compile target failed.

Although these could be addressed to a degree by improving the structure of the boilerplate LIT commands,
packaging the the pattern into a single encapsulated command instead also saves time when writing tests, and allows us to
more easily optimize the implementation in the future.

Since some Dafny features are not supported by all compile targets,
the utility allows a compile target to report errors if and only if every error reports a known unsupported feature.
See [the Feature enumeration here](../Dafny/Feature.cs) for more details.

This utility is also used to generate the [compiler feature support matrix](https://dafny.org/latest/DafnyRef/DafnyRef#sec-supported-features-by-target-language) in the reference manual. This may be moved in the future into
a `dafny` CLI option.

The following command will output the CLI help text:

```
dotnet run --project Source/TestDafny/TestDafny.csproj
```

For help on a specific verb (e.g. `for-each-compiler`):

```
dotnet run --project Source/TestDafny/TestDafny.csproj -- for-each-compiler --help
```

## Known limitations

This tool does not yet have a way to account for non-deterministic output. In particular, it is common for existing test cases
to print `set<T>` values, and the order that elements are printed in is not consistent across runtimes (nor do the language semantics
even guarantee that a given backend will pick a consistent ordering). I intend to add something similar to `OutputCheck` directives
to `*.expect` files to address this in the future.
