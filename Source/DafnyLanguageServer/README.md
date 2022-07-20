# DafnyLS

*DafnyLS* is a [language server](https://microsoft.github.io/language-server-protocol/) for [Dafny](https://github.com/dafny-lang/dafny). It is implemented in C# on .NET with OmniSharp's [C# Language Server Protocol](https://github.com/OmniSharp/csharp-language-server-protocol).


## Running

Place the [Z3 executable](https://github.com/Z3Prover/z3/releases/tag/Z3-4.8.5) in the language server's root directory or within the `z3/bin` subdirectory (already present in the [release](https://github.com/dafny-lang/dafny/releases) packages). If not on windows, ensure that the executable has execution permissions:

```sh
chmod u+x ./z3/bin/z3
```

The language server can be started either by the executable itself (e.g., `DafnyLanguageServer.exe` on windows) or with the following command.

```sh
dotnet DafnyLanguageServer.dll
```

## Configuration

The language server can be configured using the `DafnyLanguageServer.appsettings.json` file as well as using CLI arguments.

For example, if you want to configure the automatic verification through the command line:

```sh
dotnet DafnyLanguageServer.dll --documents:verify=onsave
```

Or using the `DafnyLanguageServer.appsettings.json` configuration file:

```json
{
  "Documents": {
    "Verify": "onsave"
  }
}
```

Options provided through the command line have higher priority than the options provided within `DafnyLanguageServer.appsettings.json`.


### Documents

```sh
# Sets when the automatic verification should be applied.
# Options:
# - never - Never verifies the document.
# - onchange - Verifies the document with each change.
# - onsave - Verifies the document each time it is saved.
# default: onchange
--documents:verify=onchange
```

### Verifier

```sh
# Sets maximum execution time (in seconds) for verifications
# Default: 0 (no time limit)
--verifier:timelimit=0

# Sets the maximum number of virtual cores to use. 
# Default: 0 (use half of the available virtual cores).
--verifier:vcscores=0

# Set the caching policy (like /verifySnapshots for Dafny.exe)
# Default: 0 (no caching).
--verifier:verifysnapshots=0

# Set whether or not to compute and report verification gutter statuses
# Default: 0 (no gutter status reported).
--verifier:gutterStatus=true
```

### Ghost Diagnostics

```sh
# Mark ghost statements
# Default: true (mark the statements)
--ghost:markStatements=true
```

### Plugins

```sh
# Provides a path to assemblies and optional space-separated command-line arguments after a comma.
# Repeat with --dafny:plugins:0=... --dafny:plugins:1=... for multiple plugins.
--dafny:plugins:0=path\to\example.dll
--dafny:plugins:0=path/to/example2.dll,oneArgument
--dafny:plugins:0=example3.dll,"firstArgument with \" space and quote" secondArgument

# On the command-line, you'd use the following escapes for the first and third examples:
"--dafny:plugins:0=path\\to\\example.dll"
"--dafny:plugins:0=example3.dll,\"firstArgument with \\\" space and quote\" secondArgument"

# For just the dafny executable, replace `--dafny:plugins:X` by `--plugin:` that you can repeat.
```

#### About plugins

*Plugins are experimental.
The plugin API directly exposes the Dafny AST, which is constantly evolving.
Hence, always recompile your plugin against the binary of Dafny that will be importing your plugin.*

Plugins are libraries linked to a `Dafny.dll` of the same version than the language server.
A plugin typically defines:

* Zero or one class extending `Microsoft.Dafny.Plugins.Configuration` which receives plugins arguments in their method `ParseArguments`,
  and returns a list of `Microsoft.Dafny.Plugins.Rewriter` when their method `GetRewriters()` is called by Dafny.
* Zero or more classes extending `Microsoft.Dafny.Plugins.Rewriter`.
  If a configuration class is provided, it is responsible for instantiating them and returning them in `GetRewriters()`.
  If no configuration class is provided, an automatic configuration will load every defined `Rewriter`s automatically.

The most important methods of the class `Rewriter` that plugins override are
* (experimental) `PreResolve(ModuleDefinition)`: Here you can optionally modify the AST before it is resolved.
* `PostResolve(ModuleDefinition)`: This method is repeatedly called with every resolved and type-checked module, before verification.
  Plugins override this method typically to report additional diagnostics.
* `PostResolve(Program)`: This method is called once after all `PostResolve(ModuleDefinition)` have been called.

Plugins are typically used to report additional diagnostics such as unsupported constructs for specific compilers (through the methods `Èrror(...)` and `Warning(...)` of the field `Reporter` of the class `Rewriter`)

Note that all plugin errors should use the original program's expressions' token and NOT `Token.NoToken`, else no error will be displayed in the IDE.

Morover, plugins should not write anything to `stdout` as it interferes with the communication protocol with the IDE.