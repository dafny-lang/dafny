<p></p> <!-- avoids duplicate title -->

Automatic Initialization of Variables
=====================================

Dafny is a type-safe language, which primarily means that every use of a _variable_
(local variable, parameter, bound variable, object field, or array element)
evaluates to a value of the variable's type. The type checker and verifier together
enforce that the value assigned to a variable is indeed a value of that variable's
type. Since the type of a variable never changes, this ensures type safety, provided
a variable is assigned before it is used. But what about any uses before then?

If a variable is used before it has been assigned, Dafny still arranges for the
variable to be initialized with _some_ value of the variable's type. (Since this
is a nondeterministic assignment, this behavior can be converted to a static error
by using the command-line option `/definiteAssignment:3`.) To accomplish this,
the compiler needs to have the ability to emit an expression that produces a
value of a given type. This is possible for many, but not all, types.

This document describes for which types the compiler can produce initializing
expressions and the mechanism used for doing so.

Types
-----

For reference, Dafny has the following kinds of types:

* primitive types (`int`, `real`, `char`, `bool`, bitvectors of any width, and `ORDINAL`)
* collection types (sets, multisets, sequences, and maps)
* `newtype`s (these are distinct numeric types, whose values of mimic those of the given
  numeric base type, or possibly a subset thereof)
* datatypes and co-datatypes
* arrow types (first-class function values of any arity)
* possibly-null reference types (classes, arrays of any dimension, traits)
* subset types (a subset type of a base type `B` has a subset of the values of `B`; this
  subset is characterized by a constraint on `B`)
* type parameters

In addition, there are _synonym types_ (which are just that--synonyms for other types) and
_opaque types_ (which cannot be compiled, so they don't play a role here).

Notes:
* `nat` is a built-in subset type of `int`
* `string` is a built-in type synonym for `seq<char>`
* tuple types are datatypes
* iterators give rise to class types
* collection types, datatypes, co-datatypes, arrow types, reference types, and subset
  types can have type parameters
* every possibly-null reference type `R?` has a corresponding non-null type `R`,
  predefined as the subset type `type R = r: R? | r != null`
* every arrow type `AA ~> B` (partial, heap-reading functions from the list of type `AA`
  to the type `B`) has a built-in subset type `AA --> B` (partial functions from `AA`
  to `B`), which in turn has a built-in subset `AA -> B` (total functions from `AA` to
  `B`)

Auto-init types
---------------

A type is called an _auto-init type_ if it is legal for a program to use a variable of
that type before the variable has been initialized.

All primitive types are auto-init types. For example, the following is a legal program
snippet:

    var x: int;
    var ch: char;
    print x, " ", ch, "\n";

A compiler is permitted to assign _any_ values to `x` and `ch`, so long as those values
are of types `int` and `char`, respectively. In fact, the compiler is free to choose
different values each time this program snippet is executed, even in the same run of the
program. In other words, the language allows the selection of the values to be
nondeterministic.

The purpose of this document is to describe how the compiler (in particular, the
Dafny-to-C# compiler in `Compiler-CSharp.cs`, but the other targets are similar) implements
the auto-init feature. It will be convenient (and, for this particular compiler, accurate)
to speak of each type as having a _default value_. However, please note that this
terminology is specific to an implementation of a compiler--the Dafny _language_ itself
does not have a notion of specific "default values" of types, not even for auto-init types.

Type descriptors
----------------

To obtain default values of certain type parameters, the compiler emits _run-time type descriptors_
(or just _type descriptors_ for short). A type descriptor has the ability to produce a
default value of a given type.

The C# declaration of the class of type descriptors lives in the `Dafny` namespace:

```
public class TypeDescriptor<T>
{
  private readonly T initValue;
  public TypeDescriptor(T initValue) {
    this.initValue = initValue;
  }
  public T Default() {
    return initValue;
  }
}
```

For example, consider a Dafny program where `G` is a type parameter that represents an auto-init type.
For an uninitialized local variable of type `G`, the compiler will assign the default value

    td_G.Default()

where `td_G` is type descriptor for `G`. (More on where `td_G` comes from below.)

Primitive types
---------------

Primitive types are auto-init types. Their default values are chosen to be
`false` for `bool`,
`0.0` for `real`,
`'D'` for `char`,
and `0` for `int`, bitvector types, and `ORDINAL`.

Type descriptors for these types are available as static fields in the `Dafny.Helpers` class.
For example:

```
public static readonly TypeDescriptor<bool> BOOLEAN = new TypeDescriptor<bool>(false);
public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');
public static readonly TypeDescriptor<BigInteger> INTEGER = new TypeDescriptor<BigInteger>(BigInteger.Zero);
public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
```

Since `ORDINAL` is at run time represented like `int`, it also uses the `Helpers.INTEGER` type descriptor.

Bitvectors are represented as unsigned C# integer types, if possible, and as `BigInteger` otherwise.
For this purpose, it uses the `Dafny.Helpers` fields

```
public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);
```

for bitvectors up to 8, 16, 32, and 64 bits, respectively, and uses `Helpers.INTEGER` for wider bitvectors.

Subset types
------------

A subset type `S` with list of type parameters `TT` has the form

    type S<TT> = b: B | E witness W

where `B` is the base type, `E` is a constraint (in terms of the bound variable `b`), and
`W` in the optional `witness` clause is a value that satisfies `E`.

The target representation for `S` is the same as for `B`. Nevertheless, the compiler emits a
class named `S`, which holds certain information about `S`. If `S` has a `witness` clause,
the target class `S` will contain the following field:

```
class S<TT> {
  public static readonly B Witness = W;
  //...
}
```

The target class `S` will also contain a method `_TypeDescriptor` that returns a type
descriptor for `S`. If `S` has a `witness` clause, the method is

```
public static Dafny.TypeDescriptor<B> _TypeDescriptor(TypeDescriptor<T> td_T, ...) {
  return new Dafny.TypeDescriptor<B>(Witness);
}
```

where `TypeDescriptor<T> td_T, ...` denotes one parameter for each type `T` in `TT` constrained
to be an auto-init type. A type parameter is constrained to be an auto-init type if
it bears the `(0)` suffix (called a _type characteristic).

If `S` has no type parameters, then the value returned by `_TypeDescriptor` is cached as
follows:

```
private static readonly Dafny.TypeDescriptor<B> _TYPE = new Dafny.TypeDescriptor<B>(Witness);
public static Dafny.TypeDescriptor<B> _TypeDescriptor() {
  return _TYPE;
}
```

If `S` has no `witness` clause of if it instead has a `ghost witness` clause, then
`Witness` in the body of `_TypeDescriptor` or the RHS of `_TYPE` is replaced by the default value
of type `B` (which, due to checks performed by the type checker and verifier, will
necessarily be a zero-equivalent value in C#).

To obtain a type descriptor for `S<GG>`, the compiler emits the expression

    S<G>._TypeDescriptor(td_G, ...)

where `td_G` is the type descriptor `G`, for each type `G` that corresponds to an
auto-init type parameter of `S`.

Newtypes
--------

A `newtype` declaration defines a new numeric type. It has the general form

    newtype N = x: B | E witness W

It gives rise to the declarations of `Witness` (if the type has a `witness` clause),
`_TYPE`, and `_TypeDescriptor` as described above for subset types. Note that a `newtype`
does not have any type parameters.

Collection types
----------------

The collections types, like `set<T>` and `map<T, U>`, also give rise to a `_TypeDescriptor`
method, as well as a `_TYPE` field (because the type parameters of collections type are not
auto-init). For `set<T>`, these declarations are found in `Set<T>` (note, not `ISet<T>`, since
C# doesn't allow declarations in an interface) and are:

```
private static readonly Dafny.TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
public static Dafny.TypeDescriptor<ISet<T>> _TypeDescriptor() {
  return _TYPE;
}
```

where `Empty` denotes the empty set. The other collections are similar.

