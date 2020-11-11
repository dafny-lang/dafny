# DafnyLS

[![.NET Core](https://github.com/DafnyVSCode/language-server-csharp/workflows/.NET%20Core/badge.svg)](https://github.com/DafnyVSCode/language-server-csharp/actions?query=workflow%3A%22.NET+Core%22)
[![Code coverage](https://codecov.io/github/DafnyVSCode/language-server-csharp/branch/master/graph/badge.svg)](https://codecov.io/github/DafnyVSCode/language-server-csharp/branch/master)

*DafnyLS* is a [language server](https://microsoft.github.io/language-server-protocol/) for [Dafny](https://github.com/dafny-lang/dafny). It is implemented in C# on .NET Core 3.1 with OmniSharp's [C# Language Server Protocol](https://github.com/OmniSharp/csharp-language-server-protocol).

## Building

Clone the DafnyLS repo and its submodules transitively.

```sh
git clone https://github.com/DafnyVSCode/language-server-csharp
git submodule update --init --recursive
```

When building DafnyLS from its source, the necessary build dependencies will be automatically downloaded from NuGet or built as a project reference.

```sh
dotnet build -c Release Source/
```

## Running

Place the [Z3 executable](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.4) in the language server's root directory or within the `z3/bin` subdirectory (already present in the [release](https://github.com/DafnyVSCode/language-server-csharp/releases) packages). If not on windows, ensure that the executable has execution permissions:

```sh
chmod +x ./bin/z3
```

The language server can be started either by the executable itself (e.g., `DafnyLS.exe` on windows) or with the following command.

```sh
dotnet DafnyLS.dll
```
