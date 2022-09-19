<p></p> <!-- avoids duplicate title -->

Dafny compilation of trait and class
====================================

This document describes the compilation of `trait` and `class` declarations.
Specifically, the document addresses

* `trait` and `class` declarations with type parameters and `extends` clauses
* instance members of those declarations
* compilation into the target languages C#, Java, JavaScript, and Go

The document does not include descriptions of

* `static` members
* `:extern` declarations
* how to translate a method with multiple out-parameters into languages that support
  only one (Java and JavaScript)

Member declarations
-------------------

For the purpose of compilation, there are eight kinds of member declarations:

* Mutable fields:
  `var a: X`
* Immutable fields:
  `const c: X`
* Immutable fields with a right-hand side (RHS):
  `const d: X := E`
* Body-less functions:
  `function method F<U>(x: X): Y`
* Functions with an implementation:
  `function method G<U>(x: X): Y { E }`
* Body-less methods:
  `method M<U>(x: X) returns (y: Y)`
* Methods with an implementation:
  `method N<U>(x: X) returns (y: Y) { S }`
* Constructors:
  `constructor Ctor(x: X) { S }`

Here and throughout, `X` and `Y` denote any types, `E` denotes
an expression, and `S` denotes a statement.

Preliminaries
-------------

## Target languages

When speaking in general terms about the target language, this document uses
words like "interface", "class", and "static", but meaning the target-language
equivalent of those. Such an "interface" is like a `trait` in Dafny, but with
no fields and no implementations.

## Type descriptors

The compilation of (non-reference) Dafny types to target types is many-to-one.
For example, a subset type
```dafny
type Odd = x: int | x % 2 == 1
```

compiles to the same thing as the base type `int` does. For this reason,
Dafny adds _run-time type descriptors_, which lets these types be distinguished
at run time. The primary purpose of this is to be able to find a "default"
value of a type parameter at run time. Not all type parameters need a corresponding
type descriptor, but the sections below show them everywhere. The name
`RTD` is used to denote the type of the type descriptors.

## Outline

The rest of this document presents, in order, the compilation of:

* members for simple traits (no parent traits)
* members for simple classes (no parent traits)
* members inherited from parent traits
* constructor bodies (in classes)

Compilation of traits
---------------------

Consider a trait declared as
```dafny
trait Trait<V> {
  var a: X
  const c: X
  const d: X := E
  function method F<U>(x: X): Y
  function method G<U>(x: X): Y { E }
  method M<U>(x: X) returns (y: Y)
  method N<U>(x: X) returns (y: Y) { S }
}
```

Note that a trait does not have any constructors.

A trait gets compiled into one interface and one "companion" class. Using a
Dafny-like syntax, the target of the compilation is:
```dafny
interface Trait<V> {
  function method a(): X
  method set_a(value: X)
  function method c(): X
  function method d(): X
  function method F<U>(rtdU: RTD, x: X): Y
  function method G<U>(rtdU: RTD, x: X): Y
  method M<U>(rtdU: RTD, x: X) returns (y: Y)
  method N<U>(rtdU: RTD, x: X) returns (y: Y)
}

class Companion_Trait<V> {
  static function method d(rtdV: RTD, _this: Trait<V>) { E }
  static function method G<U>(rtdV: RTD, rtdU: RTD, _this: Trait<V>, x: X): Y { E }
  static method N<U>(rtdV: RTD, rtdU: RTD, _this: Trait<V>, x: X) returns (y: Y) { S }
}
```
There is no subtype relation between `Trait` and `Companion_Trait`.
The companion class is used only as a "home" for the static methods.

For any member with an implementation (`d`, `G`, and `N`), there is both a declaration
in the interface and a corresponding definition in the companion class. The implementation
(RHS or body) of the member is compiled into the latter.

The functions and methods in the interface take a type descriptor for `U`, but not for
`V`. This is because type descriptors of the receiver object are supplied at the time
the object is created. In contrast, the implementations in the companion class
do take a type descriptor for `V`, because any type descriptors of the receiver will
be stored in the receiver in terms of the type parameters of the receiver's class.

Note: Evidently, type parameters of the trait (or class) are not in scope in
the RHS a `const` declaration. That is probably a bug. If this changes, then
method `d` in the companion class also needs to take type-descriptor parameters.

Note: Evidently, a `const` without a RHS in a trait is not allowed to be overridden (to
be given a RHS). That restriction was probably necessary under the previous encoding, but
it isn't anymore. It would be good to remove this restriction.

## C#

C# supports _properties_. Such a property is a pair of methods: a getter and a(n optional) setter.
Dafny compiles a mutable trait field into a property with a getter and setter, and compiles
an immutable field into a property with just a getter.

The immutable field `d` with a RHS still gets translated into a static function in the companion
class, since it is a static function with an parameter called `_this`.

The C# target code uses some features of reflection instead of using explicit type-descriptor
parameters.
```
interface Trait<V> {
  property a: X { get; set; }
  property c: X { get; }
  property d: X { get; }
  function method F<U>(x: X): Y
  function method G<U>(x: X): Y
  method M<U>(x: X) returns (y: Y)
  method N<U>(x: X) returns (y: Y)
}

class Companion_Trait<V> {
  static function method d(_this: Trait<V>) { E }
  static function method G<U>(_this: Trait<V>, x: X): Y { E }
  static method N<U>(_this: Trait<V>, x: X) returns (y: Y) { S }
}
```
## Java

A static method in Java cannot use the type parameters of the enclosing class. Therefore,
the companion class for Java instead adds these type parameter to the method.
```java
interface Trait<V> {
  function method a(): X
  method set_a(value: X)
  function method c(): X
  function method d(): X
  function method F<U>(rtdU: RTD, x: X): Y
  function method G<U>(rtdU: RTD, x: X): Y
  method M<U>(rtdU: RTD, x: X) returns (y: Y)
  method N<U>(rtdU: RTD, x: X) returns (y: Y)
}

class Companion_Trait {
  static function method d<V>(rtdV: RTD, _this: Trait<V>) { E }
  static function method G<V, U>(rtdV: RTD, rtdU: RTD, _this: Trait<V>, x: X): Y { E }
  static method N<V, U>(rtdV: RTD, rtdU: RTD, _this: Trait<V>, x: X) returns (y: Y) { S }
}
```

## JavaScript

Being a dynamicly typed language, objects in JavaScript are built by creating members during
object construction. This flexibility means that body-less definitions don't generate
any code.

A trait gives rise to just one main type, which is a JavaScript class. It serves the purpose
of the companion class.

Finally, since JavaScript is dynamicly typed, the language does not require (or support) type
parameters. However, compilation still generates type descriptors.

The result is thus organized as follows:
```
class Trait {
  static function method d(rtdV, _this) { E }
  static function method G(rtdV, rtdU, _this, x) { E }
  static method N(rtdV, rtdU, _this, x) { S }
}
```

The members without implementations (`a`, `c`, `F`, and `M`) are during object construction,
as described in a later section.

## Go

Go has no type parameters, so those are replaced by the empty interface type.
```
interface Trait {
  function method a(): X
  method set_a(value: X)
  function method c(): X
  function method d(): X
  function method F(rtdU: RTD, x: X): Y
  function method G(rtdU: RTD, x: X): Y
  method M(rtdU: RTD, x: X) returns (y: Y)
  method N(rtdU: RTD, x: X) returns (y: Y)
}

class Companion_Trait {
  static function method d(_this: Trait) { E }
  static function method G(rtdV: RTD, rtdU: RTD, _this: Trait, x: X): Y { E }
  static method N(rtdV: RTD, rtdU: RTD, _this: Trait, x: X) returns (y: Y) { S }
}
```

Compilation of class members
----------------------------

Consider a class declared as
```dafny
class Class<V> {
  var a: X
  const c: X
  const d: X := E
  function method G<U>(x: X): Y { E }
  method N<U>(x: X) returns (y: Y) { S }
}
```

Constructors of the class are considered in a later section. Note that all functions and
methods of a class to be compiled have bodies.

A class gets compiled into one target class. Using a Dafny-like syntax, the target of
the compilation is:
```
class Class<V> {
  var _rtdV: RTD
  var a: X
  var _c: X
  function method c(): X { _c }
  function method d(): X { E }
  function method G<U>(rtdU: RTD, x: X): Y { E }
  method N<U>(rtdU: RTD, x: X) returns (y: Y) { S }
}
```

The type descriptor for `V` is passed into the constructor (not shown here, but see
a later section) and stored in the field `_rtdV`. The functions and methods in the class
take a type descriptor for `U` and access `_rtdV` via the receiver object.

The value of the immutable field `c` is computed in the constructor (not shown here)
and therefore needs to be stored. For this purpose, the target class uses a backing
field `_c`, which is returned by the function `c()`.

Design alternative: Immutable field `d` does not need a backing store, since its value
is an expression that can easily be compiled to be evaluated each time the field is
accessed. An alternative would be to nevertheless introduce a backing store for it.
That would cost additional space in each object, but would avoid re-evaluating the
RHS `E` and would make the treatment of `c` and `d` more uniform. A possible advantage
of the current design is that it gives a way in a Dafny program to select between
the backing-stored constant and a re-evaluate constant (an argument that doesn't
apply to immutable fields inherited from traits).

Design alternative: Instead of using a backing store for immutable fields, the target
class could just declare these as fields. This would be more straightforward, though
it would requires storage in every object and wouldn't offer the possibility of
letting a Dafny program select between backing store and re-evaluation.

Note: Evidently, type parameters of the trait (or class) are not in scope in
the RHS a `const` declaration. That is probably a bug. If this changes, then
method `d` above also needs to take type-descriptor parameters. The type descriptors
must be initialized before an other initializing expression needs them.

## C#

The compilation to C# does not use type descriptors, so the `_rtdV` field is not
present and neither are the type-descriptor parameters.

The functions for retrieving `c` and `d` are declared as getter properties.
```
class Class<V> {
  var a: X
  var _c: X
  property c: X { get { _c } }
  property d: X { get { E } }
  function method G<U>(x: X): Y { E }
  method N<U>(x: X) returns (y: Y) { S }
}
```

## Java
```java
class Class<V> {
  var _rtdV: RTD
  var a: X
  var _c: X
  function method c(): X { _c }
  function method d(): X { E }
  function method G<U>(rtdU: RTD, x: X): Y { E }
  method N<U>(rtdU: RTD, x: X) returns (y: Y) { S }
}
```

## JavaScript

The compilation to JavaScript uses getters for the immutable fields.

The `_rtdV`, `a`, and `_c` fields are declared by virtue of being assigned in the
constructor. In the following, they are nevertheless shown as explicit field
declarations:

```
class Class<V> {
  var _rtdV
  var a
  var _c
  property c { get { _c } }
  property d { get { E } }
  function method G(rtdU, x) { E }
  method N(rtdU, x) { S }
}
```

## Go

Go doesn't have type parameters, but the compiler nevertheless generates type
descriptors.

```go
class Class {
  var _rtdV: RTD
  var a: X
  var _c: X
  function method c(): X { _c }
  function method d(): X { E }
  function method G(rtdU: RTD, x: X): Y { E }
  method N(rtdU: RTD, x: X) returns (y: Y) { S }
}
```

Inherited members
-----------------

Here is a trait `Parent` and two types that extend it, a trait `Trait` and a class `Class`.
Other than both extending `Parent`, types `Trait` and `Class` are unrelated.
The extending types inherit all members of `Parent` and override `F` and `M` to give
them implementations.
```dafny
trait Parent<V> {
  var a: X
  const c: X
  const d := c
  function method F<U>(x: X): X
  function method G<U>(x: X): X { E }
  method M<U>(x: X) returns (y: X)
  method N<U>(x: X) returns (y: X) { S }
}

trait Trait<V> extends Parent<W> {
  function method F<U>(x: X): Y { E }
  method M<U>(x: X) returns (y: Y) { S }
}

class Class<V> extends Parent<W> {
  function method F<U>(x: X): Y { E }
  method M<U>(x: X) returns (y: Y) { S }
}
```

The compilation of `Trait` is as follows:
```
interface Trait<V> extends Parent<W> {
}

class Companion_Trait<V> {
  static function method F<U>(rtdV: RTD, rtdU: RTD, _this: Trait<V>, x: X): Y { E }
  static method N<U>(rtdV: RTD, rtdU: RTD, _this: Trait<V>, x: X) returns (y: Y) { S }
}
```

The extending trait simply indicates its relationship to `Parent`. The overriding
member implementations are placed in the companion class, where the type of their receiver
is `Trait<V>` and where the type-descriptor parameters correspond to the type parameters of
`Trait` (not `Parent`) and the member itself.

The compilation of `Class` is as follows:
```
class Class<V> extends Trait<W> {
  var _rtdV: RTD

  var _a: X
  function method a(): X { _a }
  method set_a(value: X) { _a := value; }

  var _c: X
  function method c(): X { _c }

  function method d(): X {
    Companion_Parent<W>.d(W(_rtdV), this)
  }

  function method F<U>(rtdU: RTD, x: X): Y { E }

  function method G<U>(rtdU: RTD, x: X): Y {
    Companion_Parent<W>.G(W(_rtdV), rtdU, this, x)
  }

  method M<U>(x: X) returns (y: X) { S }

  method N<U>(rtdU: RTD, x: X) returns (y: Y) {
    y := Companion_Parent<W>.N(W(_rtdV), rtdU, this, x);
  }
}
```

As shown in a section above, the class adds a field to hold the type descriptor for `V`.

The extending class provides a backing store for the inherited mutable field and immutable
field without a RHS. Using these, it then implements the target-language inherited getters
and setters.

It implements the inherited getter for `d`, whose implementation calls the implementation
given in the companion class for `Parent`. The notation `W(_rtdV)` stands for the type
descriptor for `W` that uses `_rtdV` as the type descriptor for `V`.

The overridden members `F` and `M` are straightforwardly declared in the class.

The implementation of the inherited members `G` and `N` are given as calls to the
respective implementations in the companion class for `Parent`.

## C#

The compilation to C# uses property getters and setters for `a` and `c`.

## Java

Note: Evidently, the compiler emits a setter for `c`. It would be nice if it can be removed.

## JavaScript

As described above, but with no type parameters.

## Go

When a class or trait extends another trait `Parent` in Dafny, it instantiates the
type parameters of `Parent`. Consequently, any members inherited from `Parent` have
different type signatures than in `Parent`. This works the same way in C# and Java,
so the Dafny type signatures of overriding members get the new types. Since type
signatures are never declared in JavaScript, so this is a moot point there. In Go,
however, the lack of type parameters means that any inherited members retain their
original signatures (except for the receiver parameter).

To let the overriding body use the Dafny types, compilation to Go adds new local
variables corresponding to the formal parameters of the member. The local variables
have the instantiated types. Those corresponding to in-parameters are initialized
by a downcast of the given in-parameters. Dually, an upcast is performed at
return points.

In the following, `X` and `Y` refer to the types used in `Parent`, whereas `WX`
and `WY` refer to those types with `Parent`'s type parameter `V` replaced by
the type `W`. The Dafny-like `as` notation shows upcasts and downcasts.

```
class Class extends Trait {
  var _rtdV: RTD

  var _a: WX
  function method a(): X { _a as X }
  method set_a(value: X) { _a := value as WX; }

  var _c: WX
  function method c(): X { _c as X }

  function method d(): X {
    Companion_Parent.d(W(_rtdV), this) as X
  }

  function method F(rtdU: RTD, x: X): Y {
    var x: WX := x;
    E as Y
  }

  function method G(rtdU: RTD, x: X): Y {
    Companion_Parent.G(W(_rtdV), rtdU, this, x as WX) as WY
  }

  method M(x: X) returns (y: Y) {
    {
      var x: WX := x;
      var y: WY;
      S
      return y as Y;
    }
  }

  method N(rtdU: RTD, x: X) returns (y: Y) {
    var y: WY := Companion_Parent.N(W(_rtdV), rtdU, this, x as WY);
    return y as Y;
  }
}
```

There is no need to say `extends Trait` in Go, because trait membership is not nominal.
Nevertheless, the compiler generates some code that will cause the Go compiler to
verify `Class extends Trait` at compile time.

Note: Previously, traits were represented using a mix of a "struct" and an "interface" in Go.
In that design, the "struct" portion was embedded into the class, which allowed fields
to be inherited using Go's embedding. On the downside, this required each Dafny
object to be represented as a collection of Go objects, with mutual pointers between them
This required the compiler to insert upcasts, which became difficult to maintain in the
implementation. Moreover, the design was problematic for checking equality and became
impractical in the presence of type variance. For example, consider using a `seq<Class>` as
a `seq<Parent>`. One possibility is to copy the entire sequence, performing an upcast for
each element. This would have a large cost at run time. A more tantalizing possibility is
to always use the "main" pointer to an object when storing it in the sequence. Then, the
conversion from a `seq<Class>` to a `seq<Parent>` is a no-op. However, consider some
other `seq<Parent>` whose element include instances from a variety of classes that extend
`Parent`. Go obtain an element of that sequence as a `Parent` would require casting the
"main" object, whose type is unknown, to its `Parent` component. It would be possible to
do this if the "interface" definition of the object had a function to return the `Parent`
portion. So, rather than keeping this web of pointers among the various portions of the
object, this design was abandoned in favor of what is done for the other target languages,
where instead of a "struct" portion of a trait, the trait "interface" is used for everything
and include getters/setters for fields.

Constructors
------------

A class constructor is responsible for initializing all fields of the object. This includes
the fields declared in the class as well as the _set_ of fields inherited from ancestor
traits. Note that even if a trait is an ancestor in more than one way, there is only one
copy of its fields. (Dafny restricts programs so that every occurrences of the same ancestor
trait is given the same type parameters.)

Target languages provide various constructor mechanisms of their own. Dafny compilation
uses those only to the extent required by the target language. Each Dafny constructor
is compiled into a target-language method that performs the bulk of the work.

Consider the following declarations of a class and its ancestor traits:
```dafny
trait A<V> {
  var a: X
  const c: X
}

trait B<V> extends A<W> {
}

trait C<V> extends A<W> {
}

class Class<V> extends B<W>, C<W> {
  var k: X

  constructor Init(x: X) {
    a := x;
    c := x;
  }
}
```

The class as follows, where the target-language constructor is indicated with the
keyword `constructor` and the bulk of the work is done in a method:

```
class Class<V> extends A<W>, B<W>, C<W> {
  var _rtdV: RTD

  var _a: X
  function method a(): X { _a }
  method set_a(value: X) { _a := value; }

  var _c: X
  function method c(): X { _c }

  var k: X

  constructor (rtdV: RTD) {
    _rtdV := rtdV;
    _a := 0;
    _c := 0;
    k := 0;
  }

  method Init(x: X) {
    _a := x;
    _c := x;
    k := x;
  }
}
```

The target constructor assigns some initial values to `_a` and `_c` (to cover the
case where these are not assigned explicitly in the Dafny constructor). The RHS `0`
in these assignments is meant to be suggestive of an appropriate default value of
the appropriate type.

Note: It would be better to move the initial assignments of the fields into the
initialization method, because then the program could be analyzed to determine whether
or not those assignment are needed at all.

## C#

The compilation follows the general case, except for three things. First, type
descriptors are not used for C#. Second, the setters and getters make use of C#
properties. Third, the initial assignments to the fields are done as part of the
field declarations.

```
class Class<V> extends A<W>, B<W>, C<W> {
  var _a: X := 0
  property a: X {
    get { _a }
    set(value: X) { _a := value; }
  }

  var _c: X := 0
  property c: X {
    get { _c }
  }

  var k: X := 0

  constructor () { }

  method Init(x: X) {
    _a := x;
    _c := x;
    k := x;
  }
}
```

## Java
```java
class Class<V> extends A<W>, B<W>, C<W> {
  var _rtdV: RTD

  var _a: X
  function method a(): X { _a }
  method set_a(value: X) { _a := value; }

  var _c: X
  function method c(): X { _c }
  method set_c(value: X) { _c := value; }

  var k: X

  constructor (rtdV: RTD) {
    _rtdV := rtdV;
    _a := 0;
    _c := 0;
    k := 0;
  }

  method Init(x: X) {
    _a := x;
    _c := x;
    k := x;
  }
}
```

Note: Evidently, the Java target always uses setters when assigning to fields.

## JavaScript

Compilation to JavaScript follows the general form, except that there are no type
parameters and no need for `extends` clauses.

## Go

The compilation follows the general form, but without type parameters and no need
for `extends` clauses.
