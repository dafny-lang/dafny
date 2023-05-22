# Using Dafny from C\#

This directory shows how to call Dafny from C# (the reverse is possible as well and works similarly).  To make the example interesting we implement a small verified compiler from an arithmetic language to a stack machine.  The frontend is implemented in C# in `csharp/Main.cs`, and the backend is implemented in Dafny in `Compiler.dfy`.

## Directory listing

`Makefile`
  Build system setup

`csharp`
  C#-specific files

  `SimpleCompiler.csproj`
    C# project
  `Main.cs`
    C# part of the pipeline
  `Simple.g4`
    Grammar

`Compiler.dfy`
  Dafny part of the pipeline

`example_input.calc`
  Simple input program
`Compiler.dfy.expect`
  Prerecorded output of `dotnet run -- example_input.calc`
