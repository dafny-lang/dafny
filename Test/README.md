# Tests

Dafny test cases are based on single Dafny source files together with the expected output from the `dafny` CLI tool. 

The default behaviour is to assert that the source file verifies successfully and, for each currently-supported target language, can be compiled and run to produce the expected output.

# TODO

* More complete documentation about options (here or in the source code)
* Fix errors around missing types from System.dll when compiling to C#.
* Add `-NetCore.csproj` versions of projects as needed to support running tests using `dotnet`.
* Add support for regular expression matching against CLI output (needed to assert known limitations that cause errors with things like absolute paths names in them)
* Add support for sharding
