# Dafny compilers written in Dafny

This projects holds WIP compilers for subsets of Dafny, written in Dafny.
For an overview of the connection between CSharp and Dafny, read through https://github.com/dafny-lang/dafny/pull/1769

## Overview of the pipeline

- First we generate definitions to model the existing [`DafnyAst.cs`](../Dafny/AST/DafnyAst.cs) in Dafny.  The result is [`CSharpDafnyAST.dfy`](./CSharpDafnyAST.dfy)

- Then we write a compiler in Dafny against this interface in [`CSharp/Compiler.dfy`](CSharp/Compiler.dfy).

- Then we compile that to C# using the existing compiler, and link it with a [wrapper](CSharp/EntryPoint.cs) to get a loadable Dafny compiler plugin.

## Trying it out

Use `make run` (and read through the [`Makefile`](./Makefile) to see all the steps).
