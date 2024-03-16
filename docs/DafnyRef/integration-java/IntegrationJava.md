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
for each of the `.dfy` files. _A_`-java` will also contain 
translations to java for any library modules that are used.

A multi-language program that combines Dafny and Java
code "just" needs to be sure that the translated Dafny code fits in
to the Java code. There are two aspects to this:
- ensuring that the names of entities in the translated Dafny code are usable from Java
- ensuring that the types are the same on both sides

## **The Dafny runtime library**

The step of compiling Java files (using `javac`) requires the Dafny runtime library. That library is automatically included if `dafny` is doing the compilation,
but not if `dafny` is only doing translation.

## **Manually executing Dafny-generated Java code**

Suppose a Dafny program is contained in a `.dfy` files, `A.dfy`,
including a `Main` method.
One can build the corresponding Java program (without running it) using this command:

`dafny build --target:java A.dfy`

Alternatively, one can insert in `A.dfy` the directive `include B.dfy` and omit
B.dfy from the command-line.

The compiled program is then executed using the command
`java -cp "A-java:A-java/DafnyRuntime.jar" A`

Alternatively the build and run steps can be combined:
`dafny run --target:java A.dfy

If there is more than one `.dfy` file, general practice is to use `include` directives to include dependencies.

## **Calling Java from Dafny**

Calling a Java method from Dafny requires declaring a [shim](https://en.wikipedia.org/wiki/Shim_(computing)) in Dafny that gives a name and types
that can be referenced by Dafny code, while still being translated to the same name and types as in the Java code.

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
`dafny build --target:java Demo1.dfy Demo.java`
and then run as a Java program with
`java -cp Demo1-java:Demo1-java/DafnyRuntime.jar Demo1`

Or, in one build-and-run step: 
`dafny run --target:java Demo1.dfy --input Demo1.java`

## **Calling non-static Java methods from Dafny**

If the Java methods to be called are not static, then a receiver object 
must also be created and shared between Java and Dafny. The following example
shows how to do this.

In a `Demo1a.dfy` file:
```dafny
module {:extern "demo"} M {
  method {:extern "demo.Demo1a", "newDemo1a"} newDemo1a() returns (r: Demo1a )
  class {:extern "demo", "Demo1a" } Demo1a {
    method {:extern "demo.Demo1a", "p"} p()
  }
}
module MM {
  import opened M
  method Main() {
    var d: Demo1a := newDemo1a();
    d.p();
  }
}
```
In a `Demo1a.java` file:
```java
package demo;
public class Demo1a {
  public static Demo1a newDemo1a() { return new Demo1a(); }
  public void p() { System.out.println("Hi!\n"); }
}
```

In the Java file there are two methods: a static one that returns a new instance of the `Demo1a` class, and a non-static method that does something useful.
In the `.dfy` file we have a module `M` that has an extern name corresponding
to the package of the Java class, a class declaration that associates the
Dafny class `Demo1a` with the Java class `demo.Demo1a`, an instance method
declaration that connects the Dafny method `M.Demo1a.p` to the Java method
`demo.Demo1a.p`, and a static Dafny method `M.newDemo1a` connected to the
static Java method `demo.Demo1a.newDemo1a`.
The extern declaration for class `Demo1a` is actually not necessary if the
Dafny and Java classes have the same name and the Dafny class is contained in
a module whose extern name is the same as the Java package.

Then the `Main` method in the Dafny file calls the two Dafny methods, which are
translated to the two Java methods. The combination is built and run using
`dafny run --target:java Demo1a.dfy --input Demo1a.java`

## **Calling Dafny from Java**

The simplest way to call a Dafny method from Java is to place the Dafny method in a class within a module. The module should be attributed as {:extern "M"} where _M_ is the desired name for the _Java package_ in which the class resides.
There is no need to give an extern name to the class or the method.
For example, given this Dafny code (in `Demo2.dfy`)
```dafny
module {:extern "M"} M {
  class C {
    static method p() {
      print "Hello, World\n";
    }
  }
}
```
and this Java code (in `Demo2.java`)
```java
package demo;
public class Demo2 {
  public static void main(String... args) {
    M.C.p();
  }
}
```
then the commands
- `dafny build --target:java Demo2.dfy Demo2.java`
- `java -cp "Demo2-java:Demo2-java/DafnyRuntime.jar" demo.Demo2`
compile and run the program.
(Use `;` instead of `:` on Windows systems.)
Note that `dafny run` does not run the program as it does not know that there is a `main` method in the Java code.

If the Dafny method (say `p()`) is not a member of any class and is in the top-level 
(unnamed) module, then it is called as `_System.__default.p()`

## **Specifying class path**

The dafny build and run steps invoke `javac` and `java`. Dafny will use the version of those tools that would be invoked at a terminal prompt (e.g., the ones
found by a Linux `$PATH`). 
There is no mechanism to supply options to these internal uses of `javac` and `java`. However, `dafny` does use the value of the environment variable `CLASSPATH`. For example, if you are writing a Dafny program, `Demo.java`, which calls
methods in `Demo.jar`, you can build and run the program using
```CLASSPATH=`pwd`/Demo.jar dafny run --target:java Demo.dfy```.
The contents of the CLASSPATH must all be absolute paths.

There are two means to include other options in the build. 
First, one could create scripts named `java` and `javac` that invoke the actual `java` and `javac` with the desired options or environment settings, and then
place theses scripts on the system `$PATH`.

Alternately, one can use `dafny translate` to create the `.java` translation of the Dafny program and then use regular Java build processes to combine the
Dafny-generated Java code with other Java code.

## **Matching Dafny and Java types**

If the Java method has input arguments or an output value, then the Dafny declaration must use
corresponding types in the Dafny declaration, as shown in this table.
Here, `T'` for a type parameter `T` indicates the Java type corresponding to a Dafny type `T`.

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
| C, C? (for class, iterator C) | (class) C                   |
| (trait) T                     | (interface) T                |
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

Either there is a direct match between the Dafny-generated Java types and the types used in the Java code (as listed in the table above), or some wrapper
code is needed either on the Java side or on the Dafny side.

- If Dafny is calling a Java method in some Java library and no alterations
to the Java library are possible or desired, then the Dafny code must be written
in such a way that the Dafny types will translate directly to the Java types.
Often this requires defining a Dafny class that corresponds to the Java class.
- Alternately, one can write a Java wrapper that will translate between
the Dafny-generated (Java) types and the types used in the desired method.
The wrapper will do appropriate conversions and call the desired method.

## Performance notes

If you have the choice, given a `m: map<K, V>`, prefer iterating over the map itself like `forall k <- m` rather than over the keys `forall k <- m.Keys`. The latter currently results in `O(N²)` steps, whereas the first one remains linear.
