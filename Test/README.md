# Dafny Integration Tests

The tests in this directory are run using the [IntegrationTests](../Source/IntegrationTests) project,
which uses the xUnit-based LIT test runner from the [XUnitExtensions](../Source/XUnitExtensions) package 
rather than the LLVM `lit` CLI.

## Executing Tests from the Command Line

The xUnit LIT test interpreter is run through xUnit `Theory` parameterized tests, and therefore
hooks into the general-purpose `dotnet test` command:

```
dotnet test --logger "console;verbosity=normal" Source/IntegrationTests
```

`-logger "console;verbosity=normal"` is optional, and increases the default logging verbosity so that you can see individual tests as the pass.

The file path of each test file, relative to the `Test` directory, is used as the display name of its corresponding test.
This means you can use the `--filter` option to run a subset of tests, or even a single file:

```
dotnet test --logger "console;verbosity=normal" Source/IntegrationTests --filter DisplayName~comp/Hello.dfy
```

[See here](https://docs.microsoft.com/en-us/dotnet/core/tools/dotnet-test) for more information about
the `dotnet test` command and other supported options.

## Writing tests

Lit tests use a very restricted form of command-line: executables and their arguments piping, `>` and `>>` redirections (for respectively writing and appending stdout to a file) and `2>` and `2>>` redirections (for respectively writing and appending both stdout and stderr to a file).
To work cross-platform, use a number of macros: %verify, %resolve, %build, %run, %translate (with %trargs)
and %exits-with, %diff, %sed and others you can find defined in lit.site.cfg

Any new macros defined here must also be defied in Source/IntegrationTetss/LitTests.cs

A typical simple test for a single source file that has verification errors is
// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

There are many examples in the .dfy files under this directory.

## Executing Tests from JetBrains Rider

You will likely find it more convenient to run tests from an IDE such as
[JetBrains Rider](https://github.com/dafny-lang/dafny/wiki/JetBrains-Rider-FAQ), with a proper JDK installed like JDK 8.

Assuming you have loaded the `Dafny.sln` solution in Rider, you can execute all the integration tests
by right-clicking on the `IntegrationTests` package and selecting `Run Unit Tests`.

![Running Integration Tests in Rider](rider-run-unit-tests.png)

You will see a tree of running tests and their results, with lots of options for filtering and summarizing results.
Note the search window in the top-left, which can be used to filter to tests matching a particular substring.

![Running Integration Tests in Rider](rider-unit-tests-window.png)

Once you have at least started running these tests at least once and this tree has been populated, you can right-click any
individual test to execute it, or similarly any subset of selected tests. You will often want to start the test suite and then
immediately cancel it just to populate the tree for this purpose.

## Debugging Tests

The xUnit test runner supports executing commands such as `%dafny` by directly invoking the main entry point
of the corresponding C# package (i.e. [`DafnyDriver`](../Source/DafnyDriver)), which makes running the debugger against
a particular test much more convenient. By default this is disabled and the runner creates a separate dafny process
just as LIT does, however. This is because the main CLI implementation currently has shared static state, which
causes errors when invoking the CLI in the same process on multiple inputs in sequence, much less in parallel.
Future changes will address this so that the in-process Main invocation can be used instead, however,
which will likely improve performance but more importantly allow us to measure code coverage of the test suite.

To debug a single test, change the value of the `InvokeMainMethodsDirectly` boolean constant in the
[LitTests class](../Source/IntegrationTests/LitTests.cs) to `true`, and then right-click the test you wish to debug and select
`Debug Selected Unit Tests`. You will see exceptions if the test you are running makes multiple calls to commands like `%dafny`,
so you may wish to remove the calls you are not interested in first, e.g. if you are debugging an issue with a specific compiler.
