---
title: Integration Dafny with C# projects
---

The Dafny compilation process translates Dafny programs into target language
source code. 

For a simple Dafny-only program, the translation step converts a `A.dfy` file into `A.cs`;
the build step then produces a `A.dll`, which can be used as a library or as an executable.

A multi-language program that combines Dafny and C#
code "just" needs to be sure that the translated Dafny code fits in
to the C# code. There are two aspects to this:
- ensuring that the names of entities in the translated Dafny code are usable from C#
- ensuring that the types are the same on both sides

## Calling C# from Dafny

Calling a C# method from Dafny requires declaring a [shim](https://en.wikipedia.org/wiki/Shim_(computing)) in Dafny that gives a name and types
that can be referenced by Dafny code, while still having the same name as in the C# code.

For example, suppose we want to call a C# method `Demo.p()`. In `Demo.cs` we have
```cs
using System;
using System.IO;
public class Demo {
  public static void p() { Console.WriteLine("Hi!"); }
}
```
In `Demo1.dfy` we write,
```dafny
module M {
  method {:extern "Demo", "p"} p() 
  method Main() {
    p();
  }
}
```
Note that the declaration of `p()` has no body; it is just a declaration because the actual implementation is in C#.
Its `extern` attribute has two arguments: the fully-qualified class name and the method name.

Then the above can be built with
`dafny build --target:cs Demo1.dfy Demo.cs`
and then run as a dotnet program with
`dotnet Demo1.dll`

Or, in one build-and-run step, 
`dafny run Demo1.dfy --input Demo.cs`

## Calling non-static C# methods from Dafny

If the C# methods to be called are not static, then a receiver object
must also be created and shared between C# and Dafny. The following
example shows how to do this.

In a `Demo1a.dfy` file:
```dafny
module {:extern "demo"} M {
  method {:extern "demo.Demo", "newDemo"} newDemo() returns (r: Demo )
  class {:extern "Demo" } Demo {
    method {:extern "demo.Demo", "p"} p()
  }
}
module MM {
  import opened M
  method Main() {
    var d: Demo := newDemo();
    d.p();
  }
}
```
In a `Demo1x.cs` file
```cs
using System;
using System.IO;

namespace demo {
  public class Demo {
    public static Demo newDemo() { return new Demo(); }
    public void p() { Console.WriteLine("Hi!"); }
  }
}
```
In the C# file there are two methods: a static one that returns a new instance of the `Demo` class, and a non-static method that does something useful.
In the `.dfy` file we have a module `M` that has an extern name corresponding
to the namespace of the C# class, a class declaration that associates the
Dafny class `Demo` with the C# class `demo.Demo`, an instance method
declaration that connects the Dafny method `M.Demo.p` to the C# method
`demo.Demo.p`, and a static Dafny method `M.newDemo` connected to the
static C# method `demo.Demo.newDemo`.
The extern declaration for class `Demo` is actually not necessary if the
Dafny and C# classes have the same name and the Dafny class is contained in
a module whose extern name is the same as the C# namespace.

Then the `Main` method in the Dafny file calls the two Dafny methods, which are
translated to the two C# methods. The combination is built and run using
`dafny run --target:cs Demo1a.dfy --input Demo1x.cs`

## Calling Dafny from C#

The simplest way to call a Dafny method from C# is to place the Dafny
method in a class within a module. The module should be attributed as
`{:extern "M"}`, where _M_ is the desired name of the C# namespace in
which the C# class resides. There is no need to give an extern name to the
class or method.

In `Demo2.dfy`:
```dafny
module {:extern "MM"} MM {
  class C {
    static method p() {
      print "Hello, World\n";
    }
  }
}

module MMM {
  class Demo2x {
    static method {:extern "Demo2x", "M"} M()
  }
}

method Main() { MMM.Demo2x.M(); }
```
In `Demo2x.cs`:
```cs
public class Demo2x {
  public static void M() {
    MM.C.p(); // Calls p() in Dafny
  }
}
```

The above program is run with `dafny run --target:cs Demo2.dfy --input Demo2x.cs`.

(Note that having Dafny invoke `Main` in the `.cs` code is not yet operational.)

## Types

If the C# method has input arguments or an output value, then the Dafny declaration must use
corresponding types in Dafny:
Here, `T'` for a type parameter `T` indicates the C# type corresponding to a Dafny type `T`.
```
|-------------------------------|-----------------------------|
|  Dafny type                   |   C# type                   |
|-------------------------------|-----------------------------|
| bool                          | bool                        |
| int                           | System.Numerics.BigInteger  |
| int64                         | long                        |
| int32                         | int                         |
| int16                         | short                       |
| int8                          | sbyte                       |
| char                          | char                        |
| bitvector                     | appropriate unsigned int-based type  |
| ORDINAL                       | java.math.BigInteger        |
| real                          | Dafny.BigRational           |
|                               | double                      |
|                               | float                       |
| string                        | Dafny.ISequence<char>  |
| JavaString                    | java.lang.String                        |
| C, C? (for class, iterator C) | (class) C                   |
| (trait) T                     | (interface) T                |
| datatype, codatatype          | (class) C                   |
| subset type                   | same as base type           |
| tuple                         | \_System.\_ITuple_n_              |
| array<T>                      | T'[]                        |
| seq<T>                        | Dafny.ISequence<? extends T'> |
| set<T>, iset<T>               | Dafny.ISet<? extends T'>      |
| multisetset<T>                | Dafny.ISet<? extends T'>      |
| map<T,U>, imap<T,U>           | Dafny.IMap<? extends T'>      |
| imap<T,U>, imap<T,U>          | Dafny.IMap<? extends T'>      |
| function (arrow) types        | Func<T',U'> |
|-------------------------------|------------------------------|

