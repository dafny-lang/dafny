# Using Dafny from C\#

This directory shows how to call Dafny from C# (the reverse is possible as well and works similarly).  To make the example interesting we implement a small verified compiler from an arithmetic language to a stack machine.  The frontend is implemented in C# in `Main.cs`, and the backend is implemented in Dafny in `Compiler.dfy`.  The whole process
