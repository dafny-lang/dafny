Dafny compilation to Go
=======================

The Go backend is currently **experimental**.

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
| `char`        | `_dafny.Char`     | Defined as `rune`                 |
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
translates).

Classes
-------

Basic class functionality is mapped onto Go structs.  An instance field becomes
a field in the struct, and an instance method becomes a method of that struct.

```dafny
class Class {
    var x: int
    const y: real
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
    Y _dafny.Real // Careful!  Not constant!
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
(b) they're (often) nullable, and (c) it's necessary for our implementation of
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

Go has no inheritance.  However, we can piece together the needed functionality
using *embedding.*  An embedded struct “passes through” its fields and methods
to the embedding type.  To inherit both fields and methods, however, we need to
represent each trait using both a struct *and* an interface (in addition to the
companion object, not shown here):

```dafny
trait Trait {
    var x: int
    method f(y: real) returns (z: bool)
}
```

```go
type Trait struct {
    Iface_Trait_
    X _dafny.Int
}

type Iface_Trait_ interface {
    F(_dafny.Real) bool
}

func New_Trait_() *Trait {
    _this := Trait{}
    
    _this.X = _dafny.Zero
    
    return &_this
}
```

Calling `F` on a value of the trait will forward to the embedded `Iface_Trait_`.

The implementing class now becomes a circular data structure, where the class
embeds the trait and the trait embeds a pointer back to the full class:


```dafny
class Class extends Trait {
    var t: string
    method f(y: real) returns (z: bool) {
        ...
    }
}
```

```go
type Class struct {
    Trait
    T _dafny.Seq
}

func (_this *Class) F(y _dafny.Real) bool {
    ...
}
```

The initializer ties the knot:

```go
func New_Class_() *Class {
    _this := Class{}

    _this.T = _dafny.SeqOfString("")
    _this.Trait.Iface_Trait = &_this

    return _this
}
```

Since `Class` implements `F` *with a pointer receiver*, a `*Class` is
eligible as the value of the embedded `Iface_Trait_`.

The only remaining wrinkle is that, while the embedded types pass on their
fields and methods, `Trait` is still not a subtype of `Class`, so a variable of
type `Trait` cannot have a `Class` as its value.  The compiler deals with this
by explicitly accessing the embedded `Trait` value whenever such an *upcast*
occurs:

```dafny
var c : Class = ...
var t : Trait = c
```

```go
var c Class = ...
var t Trait = c.Trait
```

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
