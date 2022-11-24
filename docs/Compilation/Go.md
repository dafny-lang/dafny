<p></p> <!-- avoids duplicate title -->

Dafny compilation to Go
=======================

This documentation is intended primarily to help with writing Go code that makes
use of code generated from Dafny.  The emphasis is therefore on features visible
to the user of the module.

Note: Identifiers
-----------------

As much as possible, identifiers in generated code include underscores in their
names.  Therefore, to avoid namespace collisions, **avoid using underscores in
names in Dafny code** if you anticipate compiling to Go.

Top-Level Structure
-------------------

Unlike C# and JavaScript, Go imposes strict requirements on modules and file
structure.  As it is not possible to put a multi-package Go program into one
file, a whole directory structure is produced alongside the original `.dfy`
file.  For a Dafny source file `Example.dfy` which doesn't define any modules,
the structure will look like so:

  - `Example-go`: The top level, to which `GOPATH` is set in order to run the
    program.
    - `src`: All source files are placed here.
      - `Example.go`: A stub which calls the Main method in `module_/module_go`.
      - `module_/module_.go`: The main module.
      - `dafny/dafny.go`: The Dafny run-time library.
      - `System_/System_.go`: Additional definitions for built-in types.

Each Dafny module will be placed in a package named after the module, in a file
such as `Module/Module.go`.  If the module's name begins with an underscore
(such as in the `_module` and `_System` modules), the filename will move the
underscore to the end.  (Go ignores any file whose name starts with an
underscore.)

Anything declared outside of a module will end up in the default module, called
`_module`.

Predefined Types
----------------

| Dafny         | Go                |                                   |
| :------------ | :---------------- | :-------------------------------- |
| `bool`        | `bool`            |
| `int`         | `_dafny.Int`      | Immutable wrapper for `*big.Int`  |
| `bv`          | `_dafny.BV`       | Synonym of `_dafny.Int`           |
| `real`        | `_dafny.Real`     | Immutable wrapper for `*big.Real` |
| `char`        | `_dafny.Char` (`/unicodeChar:0`)<br> `_dafny.CodePoint` (`/unicodeChar:1`) | Defined as `rune`                 |
| `string`      | `_dafny.Seq`      |
| `object`      | `*interface{}`    |
| `array<X>`    | `*_dafny.Array`   |
| `A -> B`      | `func(A) B`       |
| `seq<X>`      | `_dafny.Seq`      |
| `set<X>`      | `_dafny.Set`      |
| `multiset<X>` | `_dafny.MultiSet` |
| `map<X, Y>`   | `_dafny.Map`      |

Here `big` refers to the Go built-in bignum library `"math/big"`.

Note that nullable Dafny types (`object` and `array<X>`) are modelled as pointer
types in Go so that they have the distinguished value `nil` (to which `null`
translates). In Go, each pointer type has its own `nil` value; that is, `nil`
is typed to a specific pointer type (see also discussion of `nil` in the
section on [Traits](#traits) below).

Classes
-------

Instance members of classes are described in docs/Compilation/ReferenceTypes.md.

Basic class functionality is mapped onto Go structs.  An instance field becomes
a field in the struct, and an instance method becomes a method of that struct.

```dafny
class Class {
  var x: int
  constructor(x: int) {
    this.x := x;
    ...
  }
  method Frob(z: string, c: Class) returns (a: int, b: char) {
    ...
  }
}
```

```go
type Class struct {
  X _dafny.Int
}

func (_this *Class) Ctor__(x: _dafny.Int) {
  _this.X = x
  ...
}

func (_this *Class) Frob(z dafny.Seq, c *Class) (_dafny.Int, _dafny.Char) {
  ...
}
```

**Caution:** Constant fields are represented as normal fields in generated Go
code.  There is no enforcement mechanism.  Be careful!

Note that the method has a pointer receiver, and the parameter type `Class` is
translated as the pointer type `*Class`. Objects are always translated as
pointers, including in receiver types, since (a) they're mutable in general,
(b) they may be nullable, and (c) it's necessary for our implementation of
inheritance (see [Traits](#traits)).

Note also that the constructor becomes a regular method called `Ctor__` taking
an already-allocated value as its receiver.

Finally, all field and method names are capitalized so that they are exported
from the defining module.

### Initializers

In addition to any constructors, each class also has an *initializer* which
allocates an object, with all fields given the default values for their types.
The initializer will be called <code>New_*Class*_</code>:

```go
func New_Class_() *Class {
  _this := Class{}

  _this.X = _dafny.Zero
  _this.Y = _dafny.ZeroReal

  return &_this
}
```

Note that the initializer is *not* a constructor.  Dafny constructors translate
to instance methods which are passed the output of the initializer.

(The translation currently uses `Class{}` and then a separate assignment
statement for each field, rather than putting the field values in the braces,
for internal reasons involving type parameters.)

### Static Members

Go doesn't have static members *per se*.  Typical Go code uses the module, not
the type, as the organizing structure, with supporting functions and variables
exported from the same module as the type itself.  Thus it's tempting simply to
translate static fields as global variables and static methods as non-method
functions.  Unfortunately, this invites namespace collisions, as two classes in
the same module can happily use the same name for a static member.  Therefore
(borrowing from Scala terminology) we declare a *companion object* called
`Companion_`*`Class`*`_` for each class:

```dafny
class Class {
  var x: int
  static const y = 42.0;
  static method Frob(z: string, c: Class) returns (a: int, b: char) {
    ...
  }
}
```

```go
type Class struct {
  X _dafny.Int
}

type CompanionStruct_Class_ struct {
  Y _dafny.Real
}
var Companion_Class_ = CompanionStruct_Class_ {
  Y: _dafny.RealOfString("42.0")
}

func (_this *CompanionStruct_Class_) Frob(z _dafny.Seq, c *Class) (_dafny.Int, _dafny.Char) {
  ...
}
```

## The Default Class

All methods are represented as being members of some class.  Top-level methods,
then, are static methods of the *default class,* called `Default__`.

```dafny
method Main() {
  print "Hello world!\n";
}
```

```go
type Default__ struct {
}

type CompanionStruct_Default___ {
}
var Companion_Default___ = CompanionStruct_Default___{}

func (_this *CompanionStruct_Default___) Main() {
  _dafny.Print(_dafny.SeqOfString("Hello world!"))
}
```

Traits
------

Instance members of traits are described in docs/Compilation/ReferenceTypes.md.

### nil

A class or array type is compiled into a _pointer type_ in Go. This means it
includes the Go value `nil`. A trait is compiled into a Go _interface_. Abstractly,
an interface value is either `nil` or a (value, type) pair. This means that
the Dafny `null` value for a trait may be represented either as the Go
interface value `nil` or a pair (`nil`, class pointer type).

For instance, consider the following program:

```dafny
trait Trait { }
class Class extends Trait { }
method TestNil() {
  var c: Class? := null;
  var t: Trait? := null;
  var u: Trait? := c;
  var w := c == c;
  var x := t == c;
  var y := t == t;
  var z := t == u;
}
```

This Dafny program sets all of `c`, `t`, and `u` to `null`, and therefore
also sets all four boolean variables to `true`. A simplified version of the target
code in Go for this program is:

```go
type Trait interface {
}
type Class struct {
  dummy byte
}
func TestNil() {
  var c *MyClass
  c = (*MyClass)(nil)  // c becomes nil of the pointer type *MyClass
  var t MyTrait
  t = (MyTrait)(nil)   // t becomes nil of interface type MyTrait
  var u MyTrait
  u = c                // u becomes (nil, *MyClass)

  var w bool
  w = c == c
  var x bool
  x = _dafny.AreEqual(t, c)
  var y bool
  y = _dafny.AreEqual(t, t)
  var z bool
  z = _dafny.AreEqual(t, u)
}
```

As illustrated in this example, values of Dafny class types can be compared directly
with `==` in Go, but values of other Dafny reference types need to be compared
by the runtime function `_dafny.AreEqual`, which handles the two representations of
`null`.

Datatypes
---------

### Inductive

Each inductive datatype is implemented as a struct that embeds an interface:

```dafny
datatype List = Nil | Cons(head: int, tail: List)
```

```go
type List struct {
  Data_List_
}

type Data_List_ interface {
  isList()
}
```

We could simply declare `List` as an interface type and be rid of `Data_List_`,
but then we could not give `List` concrete methods.  The interface's `isList()`
method is simply a marker to make sure no-one tries to pass off a type from
another module as a `List`.

Each constructor is a struct that implements the interface, along with a
constructor function:

```go
type List_Nil struct {}
func (List_Nil) isList() {}
func Create_Nil_() List {
  return List{List_Nil{}}
}

type List_Cons struct{
  head _dafny.Int
  tail List
}
func (List_Cons) isList() {}
func Create_Cons_(head _dafny.Int, tail List) List {
  return List{List_Cons{head, tail}}
}
```

Constructor-check predicates operate using type assertions:

```go
func (_this List) Is_Nil() bool {
  _, ok := _this.(List_Nil)
  return ok
}

func (_this List) Is_Cons() bool {
  _, ok := _this.(List_Cons)
  return ok
}
```

A destructor corresponding to only one constructor is implemented using a type
assertion:

```go
func (_this List) Dtor_head() _dafny.Int {
  return _this.(List_Cons).head
}

func (_this List) Dtor_tail() List {
  return _this.(List_Cons).tail
}
```

If multiple constructors share a destructor, its implementation will use a
`switch` on the data struct's type.

### Coinductive

A coinductive datatype has a data struct like that of an inductive datatype, but
the datatype itself is implemented as yet another interface:

```dafny
codatatype Stream = Next(shead: int, stail: Stream)
```

```go
type Stream struct {
  Iface_Stream_
}

type Iface_Stream_ {
  Get() Data_Stream_
}
```

Then, in addition to the usual constructors, a lazy constructor is provided:

```go
func (CompanionStruct_Stream_) Lazy_Stream_(f func () Stream) Stream {
  ...
}
```

The implementation allocates a value of the non-exported `lazyStream` type,
which implements `Get()` by calling `f` once then caching the returned value for
subsequent `Get()`s.

Type Parameters
---------------

Go doesn't have parameteric polymorphism, so parameterized types are implemented
by erasure: the Go type of a value whose type is a parameter is always
`interface{}`.  The compiler takes care of inserting the necessary type
assertions.

For example:

```dafny
function method Head<A>(xs: seq<A>): A requires |xs| > 0 {
  xs[0]
}
```

```go
func Head(xs _dafny.Seq) interface{} { ... }
```

(Here `Head` is actually a method of the default class's companion object, so it
should have a receiver of type `CompanionStruct_Default___`; we've
omitted this and other details for clarity throughout this section.)

Any sequence has the same type `_dafny.Seq`, and the `Head` function's signature
says it takes any sequence and may return any value.  Calls therefore often
require type assertions:

```dafny
var xs: seq<int> := ...;
var x: int := Head(xs);
```

```go
xs := ...
x := Head(xs).(_dafny.Int)
```

In more complex situations, it is necessary to retain type information that
would otherwise be erased.  For example:

```dafny
method GetDefault<A(0)>() returns (a: A) { }
```

Here we cannot simply compile `Default` with type `func() interface{}`—what
would it return?  Thus the compiled method takes a *run-time type descriptor*
(RTD) as a parameter:

```go
func GetDefault(A _dafny.Type) interface{} {
  var a interface{} = A.Default()
  return a
}
```

The `_dafny.Type` type is a simple interface; currently its only purpose is to
allow for zero initialization in precisely such cases as these:

```go
type Type interface {
  Default() interface{}
}
```

Each compiled class or datatype comes with a function called
<code>Type_*Class*_</code> that takes a `_dafny.Type` for each type parameter
and returns the `_dafny.Type` for the class or datatype.

Iterators
---------

An iterator is translated as a class with a `MoveNext()` method, as in Dafny.
The constructor fires off a goroutine for the body of the iterator.  As
goroutines are lightweight, this should not impose too much overhead.  One
caveat as that we have to use a finalizer to end the goroutine early if the
iterator is garbage-collected, as otherwise the goroutine stays live
indefinitely, leaking any memory it holds onto.  Because of the way finalizers
are invoked, however, the memory retained by the iterator cannot be reclaimed
until the GC *after* the iterator itself is collected.  In the worst case,
several iterators could be chained together, therefore taking n GC cycles to
clean up n iterators.

Externs
-------

Dafny code may freely interoperate with existing Go code using `{:extern}`
declarations.  This may include both pre-existing Go modules and modules written
specifically to interact with compiled Dafny code.

Go modules to be included as part of the compiled code should be passed as
additional arguments on the Dafny command line.

An `{:extern}` declaration on a module indicates that the module is
external—either one that was passed on the command line or one from a
pre-existing package.

```dafny
module {:extern "os"} OS { }
```

```go
import "os"
```

Import statements are automatically inserted in the default module and in
subsequent (non-extern) modules (this may produce problems; see
[this TODO item](#extern-always-imported)).

As a special case, types and values in the built-in top-level scope in Go can be
accessed by passing the empty string as the package name (see the next example).
Such a declaration does not generate an `import` statement.

An interface can be imported in Dafny code by declaring it as a trait with an
`{:extern}` annotation:

```dafny
module {:extern ""} Builtins {
  trait {:extern} error {
    method {:extern} Error() returns (s : string)
  }
}
```

Similarly, a class with methods can be imported, and a top-level function can
be imported as a module-level method:

```dafny
module {:extern "bufio"} BufIO {
  class {:extern} Scanner {
    method {:extern} Scan() returns (ok: bool)
    method {:extern} Text() returns (text: string)
  }

  method {:extern} NewScanner(r: OS.Reader) returns (s: Scanner)
}
```

The alert reader may notice here that the `Reader` interface belongs to the `io`
package, not `os`.  Unfortunately, extern modules must abide by Dafny's
restriction that a class can only extend a trait in its own module.  In Go
terms, then, we can't directly express that a struct in one module implements
an interface from another one.

Fortunately, there is a “cheat”:

```dafny
module {:extern "io"} IO { }

module {:extern "os"} OS {
  import Builtins

  trait {:extern "io", "Reader"} Reader { }
  class {:extern} File extends Reader { }
  method {:extern} Open(name: string) returns (file:File, error: Builtins.error?)
}
```

Here we declare an empty module for `io` just to be sure that `io` gets
imported.  Then we use a special two-argument `{:extern}` form that specifies
that `Reader` actually lives in the `io` namespace.  Dafny will understand that
we can call `Open` and use the `File` returned as a `Reader`.

TODO
----

  - [ ] There isn't always enough run-time type information to determine whether
    a sequence is a string (that is, a `seq<char>`).  In particular, a value
    created as a `seq<A>` will always be output as a sequence of individual `A`
    values rather than as a string, even if `A` is `char` for a particular
    invocation.

  - [ ] <a id="extern-always-imported"></a>Currently
    it is assumed that, once an `extern` module is declared, every
    subsequent Dafny module (plus the default module) imports it.  If a module
    does not, the Go compiler will complain about an unused import.  To avoid
    this, it suffices to declare a dummy variable of a type exported by that
    module or a dummy function that calls a function exported by it.

  - [ ] All symbols are exported from all modules (by capitalizing their names).
    There isn't yet a way to hide internal fields, methods, etc.

  - [ ] Coercion to and from native datatypes currently only happens for method
    calls, not field accesses.

  - [ ] Go implements a `switch` on a type as a linear search.  There are a few
    places where we switch on the type of a datatype value's data struct.  It
    would probably be better to replace these by separate implementations of
    functions.
