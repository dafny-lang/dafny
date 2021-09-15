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

### Documents

It is possible to change the moment when a document is verified by providing the `--documents:verify` command-line argument. The options are:

- *never* - Never verifies the document.
- *onchange* (default) - Verifies the document with each change.
- *onsave* - Verifies the document each time it is saved.

For example, to launch DafnyLS to only verify upon saving the document, use the following command:

```sh
dotnet DafnyLanguageServer.dll --documents:verify=onsave
```

### Verifier


You may specify a verification time limit (in seconds) using `--verifier:timeout`. For example, for a timeout of three seconds start the language server as follows:

```sh
dotnet DafnyLanguageServer.dll --verifier:timeout=3
```
