# 1. Introduction

Dafny [@Leino:Dafny:LPAR16] is a programming language with built-in specification constructs,
so that verifying a program's correctness with respect to those specifications
is a natural part of writing software.
The Dafny static program verifier can be used to verify the functional
correctness of programs.
This document is a reference manual for the programming language and a user guide
for the dafny tool that performs verification and compilation to an
executable form.

The Dafny programming language is designed to support the static
verification of programs. It is imperative, sequential, supports generic
classes, inheritance and abstraction, methods and functions, dynamic allocation, inductive and
co-inductive datatypes, and specification constructs. The
specifications include pre- and postconditions, frame specifications
(read and write sets), and termination metrics. To further support
specifications, the language also offers updatable ghost variables,
recursive functions, and types like sets and sequences. Specifications
and ghost constructs are used only during verification; the compiler
omits them from the executable code.

The `dafny` verifier is run as part of the compiler. As such, a programmer
interacts with it in much the same way as with the static type
checker—when the tool produces errors, the programmer responds by
changing the program’s type declarations, specifications, and statements.

(This document typically uses "Dafny" to refer to the programming language
and "dafny" to refer to the software tool that verifies and compiles programs
in the Dafny language.)

The easiest way to try out Dafny is to [download](https://github.com/dafny-lang/dafny/releases) it
to run it on your machine as you follow along with the [Dafny tutorial](../OnlineTutorial/guide).
Dafny can be run from the command line (on Linux, MacOS, Windows or other platforms) or from an IDE
such as emacs or an editor such as VSCode, which can provide syntax highlighting without
the built-in verification.

The verifier is powered
by [Boogie](http://research.microsoft.com/boogie)
[@Boogie:Architecture;@Leino:Boogie2-RefMan;@LeinoRuemmer:Boogie2]
and [Z3](https://github.com/z3prover) [@deMouraBjorner:Z3:overview].

From verified programs, the `dafny` compiler can produce code for a number
of different backends:
the .NET platform via intermediate C\# files, Java, Javascript, Go, and C++.
Each language provides a basic Foreign Function Interface (through uses of `:extern`)
and a supporting runtime library.
However, there is no automatic FFI generator, so `:extern` stubs must be written by hand.

This reference manual for the Dafny verification system is
based on the following references:
[@Leino:Dafny:LPAR16],
[@MSR:dafny:main],
[@LEINO:Dafny:Calc],
[@LEINO:Dafny:Coinduction],
[Co-induction Simply](http://research.microsoft.com/en-us/um/people/leino/papers/krml230.pdf).

The main part of the reference manual is in top down order except for an
initial section that deals with the lowest level constructs.

The details of using (and contributing to) the dafny tool are described in the User Guide ([Section 24](#sec-user-guide)).

## 1.1. Dafny Example
To give a flavor of Dafny, here is the solution to a competition problem.

```dafny
{% include_relative examples/Example-RM.dfy %}
```

