# Tests

Dafny test cases are based on single Dafny source files together with the expected output from the `dafny` CLI tool. If the source file is named `Foo.dfy`, the expected output will contained in the file named `Foo.dfy.expect`.

The default behaviour is to assert that the source file verifies successfully and, for each currently-supported target language, can be compiled and run to produce the expected output. When the behaviour is not 100% consistent between different target languages, expected discrepancies can be recorded in additional files with the name `Foo.dfy.<language>.expect`. For example: [Test/comp/NativeNumbers.dfy.js.expect](Test/comp/NativeNumbers.dfy.js.expect). Such exceptions are automatically flagged as "known issues" and classified as a "skipped/ignored" test.

Test cases are configured and run using xUnit's support for parameterized tests, with extensions for running test cases in parallel. The sets of options passed to `dafny` can be configured using YAML embedded in the first multi-line comment in the source file. Lists of values are interpreted as multiple parameterizations. For example: [Test/dafny4/git-issue250.dfy](Test/dafny4/git-issue250.dfy).

For details and more configuration options, see [the DafnyTests.cs source](Test/DafnyTests/DafnyTests.cs).

# TODO

* More complete documentation about options (in this file or in the source code)
* Depend on only the project's output directory instead of the Binaries/Test directories
  * This is mostly working except for errors around missing types from System.dll when compiling to C#
* Add support for regular expression matching against CLI output (needed to assert known limitations that cause errors with things like absolute paths names in them)
* Expose test case options as traits so that they can be filtered on (e.g. `dotnet test --filter compileTarget=java`)
* Finish converting the rest of the test cases
  * Will write a small script to do this automatically for all recognized combinations of lit `// RUN` commands
* Extract most of the xUnit extensions as a separate package, since most of it is generically useful for any other data-driven xUnit tests.
