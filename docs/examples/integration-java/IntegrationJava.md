The Dafny compilation process translates Dafny programs into target language
source code, compiles those to Java .class files, and then potentially runs the result. 

The Dafny-to-Java compiler writes out the translated files of a file _A_`.dfy`
to a directory _A_`-java`. The `-out` option can be used to choose a
different output directory. The file _A_`.dfy` is translated to _A_`.java`,
which is placed in the output directory along with helper files.
If more than one `.dfy` file is listed on the command-line, then the output
directory name is taken from the first file, and `.java` files are written
for each of the `.dfy` files. _A_`-java` will alos likely contain 
translations to java for any library modules that are used.

A multi-language program that combines Dafny and Java
code "just" needs to be sure that the translated Dafny code fits in
to the Java code. There are two aspects to this:
- ensuring that the names of entities in the translated Dafny code are usable from Java
- ensuring that the types are the same on both sides

#### Calling Java from Dafny

Calling a Java method from Dafny requires declaring a shim in Dafny that gives a name and types
that can be referenced by Dafny code, while still having the same name as in the Java code.

For example, suppose we want to call a Java method `demo.Demo.p()`. In `Demo.java` we have
```java
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

If the Java method has input arguments or an output value, then the Dafny declaration must use
corresponding types in Dafny:
```
|+-----------------------------+|+---------------------------+|
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
| multisetset<T>                | dafny.DafnySet<? extends T'>      |
| map<T,U>, imap<T,U>           | dafny.DafnyMap<? extends T'>      |
| imap<T,U>, imap<T,U>           | dafny.DafnyMap<? extends T'>      |
| function (arrow) types        | java.util.function.Function<T',U'> |
|-------------------------------|------------------------------|

The only type for which there is a bit of disconnect is `string`.

TODO


#### Calling Dafny from Java

To call a Dafny method from Java we again need to give the Dafny method a name
that is known by Java using `{:extern}` attributes. This time it is the Dafny metehod that has a body.

So a Dafny method meant to be called from Java would be written like this example:
```
module M {
  class C {
    static {:extern "demo.Demo", "m"} method m() {
      print "Hi!\n";
    }
  }
}
```
Where the new name given in the `{:extern}` attribute is the same as the Dafny name, the name can be omitted in the attribute.
Also note that all top-level Dafny declarations, which are not in an
explicit module, are translated to be in the `_System` Java package, 
and all declarations in a module that are not members of a type (such as a class) are translated to be in the `__default` Java class.

Given the above Dafny code, the method `m` can be called from Java as
`demo.mymodule.C.m();`.




#### Calling Java from Dafny
