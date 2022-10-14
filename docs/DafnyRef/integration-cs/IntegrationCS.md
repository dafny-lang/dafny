The Dafny compilation process translates Dafny programs into target language
source code. 

For a simple Dafny-only program, the translation step converts a `A.dfy` file into `A.cs`;
the biuld step then produces a `A.dll`, which can be used as a library or as an executable.

A multi-language program that combines Dafny and C#
code "just" needs to be sure that the translated Dafny code fits in
to the C# code. There are two aspects to this:
- ensuring that the names of entities in the translated Dafny code are usable from C#
- ensuring that the types are the same on both sides

#### Calling C# from Dafny

Calling a C# method from Dafny requires declaring a shim in Dafny that gives a name and types
that can be referenced by Dafny code, while still having the same name as in the C# code.

For example, suppose we want to call a C# method `demo.Demo.p()`. In `Demo.cs` we have
```cs
package demo;
public class Demo {
  public static void p() { System.out.println("Hi!\n"); }
}
```
In `Demo1.dfy` we write,
```dafny
module M {
  method {:extern "demo.Demo", "p"} p() 
  method Main() {
    p();
  }
}
Note that the declaration of `p()` has no body; it is just a declaration because the actual implementation is in Java.
Its `extern` attribute has two arguments: the fully-qualified class name and the method name.

Then the above can be built with
`dafny build -t:java Demo1.dfy Demo.java`
and then run as a Java program with
`java -cp Demo1-java:Demo1-java/DafnyRuntime.jar Demo1`

Or, in one build-and-run step, 

`dafny run Demo1.dfy Demo.java`

If the C# method has input arguments or an output value, then the Dafny declaration must use
corresponding types in Dafny:
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
| (trait) T                     | (iterator) T                |
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

The only type for which there is a bit of disconnect is `string`.


Aspects not yet implemented fully:
- Calling non-static functions and methods
- Calling Dafny from C#
- Conversion between Dafny and C# strings
