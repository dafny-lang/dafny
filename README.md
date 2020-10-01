# language-server-csharp

## Building

Clone the DafnyLS repo and its submodules transitively.

```sh
git clone https://github.com/DafnyVSCode/language-server-csharp
git submodule update --init --recursive
```

Build the dependencies before building DafnyLS itself.

```sh
dotnet build DafnyLS.sln
```

## Running

Place the Z3 executable (`z3.exe` on Windows) in the working directory of the language server or in the path. You may grab it from one of the pre-packaged [dafny releases](https://github.com/dafny-lang/dafny/releases).
