# Automatically generating Dafny traits from C# code

This directory demonstrates `AutoExtern`, a Dafny tool that implements limited
support for automatically generating trait hierarchies from C# classes.

For a primer on C#/Dafny interop, see the [`Simple_compiler`
tutorial](../Simple_compiler/) instead, which shows how to model C# types and
functions and access them from Dafny.  This tutorial uses the automated bindings
generator to save some modeling effort.

## Directory listing

`Library/`
  The C# library that this example generates Dafny bindings for. We use a
  separate project because `AutoExtern` needs to compile the project to extract
  semantic information from it.

  `LinkedLists.cs`
  `LinkedLists.cs`
    C# type definitions used by `Interop/Main.cs`.  The Dafny model for this part is generated automatically.

  `ExactArithmetic.cs`
    More C# code used by `Interop/Main.cs`.  The Dafny model for this part is written by hand (to give an example of `--rewrite`).

  `Library.csproj`
    C# project

`ClientApp/`
  A client application written in C# + Dafny that uses `Library`.

  `Makefile`
    Build system setup
  `ClientApp.csproj`
    C# project

  `GroceryListPrinter.dfy`
    Dafny code that operates directly on C# values
  `Main.cs`
    C# program that constructs a value and passes it to Dafny

  `GroceriesModel.template.dfy`
    Template file that the model generator fills in to create `GroceriesModel.dfy`.
  `GroceriesModel.dfy`
    Auto-generated Dafny model of `Library/Groceries.cs` used by `GroceryListPrinter.dfy`.

  `GroceryListPrinter.dfy.expect`
    Prerecorded output of `dotnet run`
