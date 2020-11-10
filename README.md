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

Place the Z3 executable in the language server's root directory or within the `z3/bin` subdirectory (already present in the [release](https://github.com/DafnyVSCode/language-server-csharp/releases) packages). If not on windows, ensure that the executable has execution permissions:

```sh
chmod +x ./bin/z3
```

The language server can be started either by the executable itself (e.g., `Dafny.exe` on windows) or with the following command.

```
dotnet Dafny.dll
```
