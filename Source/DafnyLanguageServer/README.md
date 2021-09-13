# DafnyLS

*DafnyLS* is a [language server](https://microsoft.github.io/language-server-protocol/) for [Dafny](https://github.com/dafny-lang/dafny). It is implemented in C# on .NET 5.0 with OmniSharp's [C# Language Server Protocol](https://github.com/OmniSharp/csharp-language-server-protocol).


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

It is possible to change the moment when a document is verified by providing the `--documents:verify` command-line argument. The options are:

- *never* - Never verifies the document.
- *onchange* (default) - Verifies the document with each change.
- *onsave* - Verifies the document each time it is saved.

For example, to launch DafnyLS to only verify upon saving the document, use the following command:

```sh
dotnet DafnyLanguageServer.dll --documents:verify=onsave
```

### Verifier

```sh
# Sets maximum execution time for verifications
# Default: 10
--verifier:timeout=10

# Sets the maximum number of virtual cores to use. 
# Default: 0 (use half of the available virtual cores).
--verifier:cores=0

# How many verification snapshots boogie can make.
# Default: 3
--verifier:snapshots=3
```
