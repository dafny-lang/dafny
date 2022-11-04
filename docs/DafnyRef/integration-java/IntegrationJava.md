---
title: Integrating Dafny and Java code
---

The Dafny compilation process translates Dafny programs into target language
source code, compiles those to Java .class files, and then potentially runs the result. 

The Dafny-to-Java compiler writes out the translated files of a file _A_`.dfy`
to a folder _A_`-java`. The `-out` option can be used to choose a
different output folder. The file _A_`.dfy` is translated to _A_`.java`,
which is placed in the output folder along with helper files.
If more than one `.dfy` file is listed on the command-line, then the output
folder name is taken from the first file, and `.java` files are written
for each of the `.dfy` files. _A_`-java` will also likely contain 
translations to java for any library modules that are used.

A multi-language program that combines Dafny and Java
code "just" needs to be sure that the translated Dafny code fits in
to the Java code. There are two aspects to this:
- ensuring that the names of entities in the translated Dafny code are usable from Java
- ensuring that the types are the same on both sides

## **The Dafny runtime library**

The step of compiling Java files (using `javac`) requires the Dafny runtime library. That library is automatically included if dafny is doing the compilation,
but not if dafny is only doing translation..

## **Manually executing Dafny-generated Java code**

Suppose a Dafny program is contained in two `.dfy` files, `A.dfy` and `B.dfy`, with `A.dfy` containing a `Main` method. One can build the corresponding Java program (without running it) using this command:

`dafny build --target:java A.dfy B.dfy`

Alternatively, one can insert in `A.dfy` the directive `include B.dfy` and omit
B.dfy from the command-line.

The compiled program is then executed using the command
`java -cp "A-java:A-java/DafnyRuntime.jar" A`

Alternatively the build and run steps can be combined:
`dafny run --target:java A.dfy --input B.dfy `

## **Calling Java from Dafny**

Calling a Java method from Dafny requires declaring a shim in Dafny that gives a name and types
that can be referenced by Dafny code, while still having the same name and types as in the Java code.

For example, suppose we want to call a Java method `demo.Demo1.p()`. In `Demo1.java` we have
```java
package demo;
public class Demo1 {
  public static void p() { System.out.println("Hi!\n"); }
}
```
In `Demo1.dfy` we write,
```dafny
module M {
  method {:extern "demo.Demo1", "p"} p() 
  method Main() {
    p();
  }
}
```
Note that the declaration of `p()` has no body; it is just a declaration because the actual implementation is in Java.
Its `extern` attribute has two arguments: the fully-qualified class name and the method name.

Then the above can be built with
`dafny build -t:java Demo1.dfy Demo.java`
and then run as a Java program with
`java -cp Demo1-java:Demo1-java/DafnyRuntime.jar Demo1`

Or, in one build-and-run step, 

`dafny run -t:java Demo1.dfy --input Demo1.java`

## **Calling Dafny from Java**

The simplest way to call a Dafny method from Java is to place the Dafny method in a class within a module. The module should be attributed as {:extern "M"} where _M_ is the desired name for the _Java package_ in which the class resides.
There is no need to give an extern name to the class or the method.
For example, given this Dafny code (in Demo2.dfy)
```
module {:extern "M"} M {
  class C {
    static method p() {
      print "Hello, World\n";
    }
  }
}
```
and this Java code (in Demo2.java)
```
package demo;
public class Demo2 {
  public static void main(String... args) {
    M.C.p();
  }
}
```
then the commands
- `dafny build -t:java Demo2.dfy Demo2.java`
- `java -cp "Demo2-java:Demo2-java/DafnyRuntime.jar" demo.Demo2`
compile and run the program.
Note that `dafny run` does not run the program as it does not know that there is a `main` method in the Java code.

If the Dafny method (say `p()`) is not a member of any class and is in the top-level 
(unnamed) module, then it is called as `_System.__default.p()`

## **Specifying class path**

The dafny build and run steps invoke `javac` and `java`. Dafny will use the version of those tools that would be invoked at a terminal prompt (e.g., the ones
found by a Linux `$PATH`). 
## **Matching Dafny and Java types**

If the Java method has input arguments or an output value, then the Dafny declaration must use
corresponding types in the Dafny declaration:

|-------------------------------|-----------------------------|
|  Dafny type                   |   Java type                 |
|-------------------------------|-----------------------------|
| bool                          | boolean                     |
| int                           | java.math.BigInteger        |
| int64                         | long                        |
| int32                         | int                         |
| int16                         | short                       |
| int8                          | byte                        |
| char                          | char                        |
| bitvector                     | appropriate int-based type  |
| ORDINAL                       | java.math.BigInteger        |
| real                          | dafny.BigRational           |
|                               | double                      |
|                               | float                       |
| string                        | dafny.DafnySequence<? extends Character>  |
| JavaString                    | java.lang.String                        |
| C, C? (for class, iterator C) | (class) C                   |
| (trait) T                     | (iterator) T                |
| datatype, codatatype          | (class) C                   |
| subset type                   | same as base type           |
| tuple                         | dafny.Tuple_n_              |
| array<T>                      | T'[]                        |
| seq<T>                        | dafny.DafnySequence<? extends T'> |
| set<T>, iset<T>               | dafny.DafnySet<? extends T'>      |
| multiset<T>                | dafny.DafnySet<? extends T'>      |
| map<T,U>, imap<T,U>           | dafny.DafnyMap<? extends T'>      |
| imap<T,U>, imap<T,U>           | dafny.DafnyMap<? extends T'>      |
| function (arrow) types        | java.util.function.Function<T',U'> |
|-------------------------------|------------------------------|

The only type for which there is a bit of disconnect is `string`.


## Aspects not yet implemented fully:

- Having a .jar file on the build or run command-line
- Calling non-static Java functions and methods from Dafny
- Conversion between Dafny and Java strings
