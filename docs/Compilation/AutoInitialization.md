<p></p> <!-- avoids duplicate title -->

Automatic Initialization of Variables
=====================================

Dafny is a type-safe language, which primarily means that every use of a _variable_
(local variable, parameter, bound variable, object field, or array element)
evaluates to a value of the variable's type. The type checker and verifier together
enforce that each value assigned to a variable is indeed a value of that variable's
type. Since the type of a variable never changes, this ensures type safety, provided
a variable is assigned before it is used. But what about any uses before then?

If a variable is used before it has been assigned, Dafny still arranges for the
variable to be initialized with _some_ value of the variable's type.
To accomplish this, the compiler needs to have the ability to emit an expression that
produces a value of a given type. This is possible for many, but not all, types.

This document describes for which types the compiler can produce initializing
expressions and the mechanism used for doing so.

Types
-----

Dafny supports the following kinds of types:

* primitive types (`int`, `real`, `bool`, `char`, bitvectors of any width, and `ORDINAL`)
* `newtype`s (these are distinct numeric types, whose values of mimic those of the given
  numeric base type, or possibly a subset thereof)
* possibly-null reference types (classes, arrays of any dimension, traits)
* type parameters
* collection types (sets, multisets, sequences, and maps)
* datatypes and co-datatypes
* arrow types (first-class function values of any arity)
* subset types (a subset type of a base type `B` has a subset of the values of `B`; this
  subset is characterized by a constraint on `B`)

In addition, there are _type synonyms_ (which are just that--synonyms for other types) and
_opaque types_ (which cannot be compiled, so they don't play a role here).

Notes:
* `nat` is a built-in subset type of `int`
* `string` is a built-in type synonym for `seq<char>`
* tuple types are built-in datatypes
* iterators give rise to class types
* collection types, datatypes, co-datatypes, arrow types, reference types, and subset
  types can have type parameters
* every possibly-null reference type `R?` has a corresponding non-null type `R`,
  predefined as the subset type `type R = r: R? | r != null`
* every arrow type `AA ~> B` (partial, heap-reading functions from the list of type `AA`
  to the type `B`) has a built-in subset type `AA --> B` (partial functions from `AA`
  to `B`), which in turn has a built-in subset `AA -> B` (total functions from `AA` to
  `B`)

Compilation of types
--------------------

The compilation of types involves several notions, defined here.

The _target type_ of a Dafny type `T` is the target-language type used to represent `T`.
The target type may not be unique to one Dafny type; in other words, several Dafny
types may compile to the same target type.

type                            | C# target type
--------------------------------|---------------------------------------------------
`int`                           | `BigInteger`
`real`                          | `BigRational`
`bool`                          | `bool`
`char`                          | `char` (for `/unicodeChar:0`)<br>`Rune` (for `/unicodeChar:1`)
bitvectors                      | `byte`, `ushort`, `uint`, `ulong`, or `BigInteger`
`ORDINAL`                       | `BigInteger`
integer-based `newtype`         | bounded C# integer or `BigInteger`
real-based `newtype`            | `BigRational`
`trait Tr`                      | interface `Tr`
`class Cl`                      | class `Cl`
`array<T>`, `array2<T>`, ...    | `T[]`, `T[,]`, ...
type parameter `T`              | `T`
collection type                 | `ISet<T>`, `IMultiset<T>`, `ISequence<T>`, `IMap<T, U>`
datatype or co-datatype `D`     | interface of class `D`
`TT ~> U`                       | `System.Func<TT, U>`
subset type for a base type `B` | `B`

The compilation of a type may emit some fields and methods that are used at run time.
These are emitted into a _companion class_. In some cases, the companion class is the
same as the target type, in some other case the companion class is a separate class,
and in other cases there is no companion class at all.

type                            | companion class
--------------------------------|---------------------------------------------------
`int`                           | none
`real`                          | none
`bool`                          | none
`char`                          | none
bitvectors                      | none
`ORDINAL`                       | none
`newtype` `T`                   | `T`
`trait Tr`                      | `_Companion_Tr`
`class Cl`                      | `Cl`
`array<T>`, `array2<T>`, ...    | none
type parameter `T`              | none
collection type                 | `Set<T>`, `Multiset<T>`, `Sequence<T>`, `Map<T, U>`
datatype or co-datatype `D`     | class `D`
`TT ~> U`                       | none
subset type `T`                 | `T`

Types can have type parameters. For a target language that supports type parameters, each
_formal_ type parameter is compiled into a corresponding formal type parameter in the target
language, and each _actual_ type argument is compiled to that type's target type.

Because target types are not unique, the type arguments passed as required by the target
language do not carry all information that is needed about the type at run time.
Therefore, the Dafny compiler augments the target language's type parameters by a
system of _type descriptors_. These are described in a section below.

Type descriptors are passed only for type parameters that bear the Dafny type characteristic
`(0)`. Such type parameters are called _auto-init type parameters_.

For inductive datatypes, the compiler uses one more notion of types, namely the
_used type parameters_. This refers to those type parameters that play a role in the
creation of a value of the datatype's "grounding constructor", explained below.

Auto-init types
---------------

A type is called an _auto-init type_ if it is legal for a program to use a variable of
that type before the variable has been initialized.

For example, `char` is an auto-init type. Therefore, the following is a legal program
snippet:

    var ch: char;
    print ch, "\n";  // this uses ch before ch has been explicitly assigned

A compiler is permitted to assign _any_ value to `ch`, so long as that value is of
type `char`. In fact, the compiler is free to emit code that chooses a different
initial value each time this program snippet is encountered at run time. In other words,
the language allows the selection of the values to be nondeterministic.

The purpose of this document is to describe how the common compilers implement
the auto-init feature. It will be convenient (and, for this particular compiler, accurate)
to speak of each type as having a _default value_. However, please note that this
terminology is specific to an implementation of a compiler--the Dafny _language_ itself
does not have a notion of specific a "default value" of any type, not even for auto-init
types.

Default-valued expressions
--------------------------

To fabricate default values, the compiler emits a _default-valued expression_.
A default-valued expression is simply an expression that evaluates to a default value
for the type.

type                                             | default-valued expression
-------------------------------------------------|------------------------------------------
`int`                                            | `BigInteger.Zero`
`real`                                           | `BigRational.ZERO`
`bool`                                           | `false`
`char`                                           | `D`
bitvectors                                       | `0` or `BigInteger.Zero`
`ORDINAL`                                        | `BigInteger.Zero`
integer-based `newtype` without `witness` clause | same as for base type, cast appropriately
real-based `newtype` without `witness` clause    | same as for base type, cast appropriately
`newtype` `NT` with `witness` clause             | `NT.Witness`
possibly-null reference types                    | `null`
non-null array types                             | empty array of the appropriate type
type parameter `T`                               | `td_T.Default()`
collection type `C<TT>`                          | `C<TT>.Empty`
datatype or co-datatype `D<TT>`                  | `D<TT>.Default(E, ...)`
`TT ~> U`                                        | `null`
`TT --> U`                                       | `null`
subset type without `witness` clause             | same as for base type
subset type `S<TT>` with `witness` clause        | `S<TT>.Default()`

Other types do not have default-valued expressions.

Here are some additional explanations of the table:

## Subset types

In a subset type with a `witness` clause, like

    type S<TT> = x: B | E witness W

the witness is used as the default value. It is returned by the `Default()` method that is emitted
in the companion class of the subset type:

```
public static B Default() {
  return W;
}
```

If the subset type has no type parameters, then the witness is pre-computed and reused:

```
private static readonly B Witness = W;
public static B Default() {
  return Witness;
}
```

Note that a witness is used as the default value only if the type has a `witness` clause; if
the type has no `witness` clause or if it has a `ghost witness` clause, then the default expression
is that of the base type.

## Newtypes

As for subset types, when a `newtype` has a `witness` clause, the witness expression is used as the
default value of the type. However, since a `newtype` does not have any type parameters, the value
is always pre-computed into a (public) `Witness` field, and that field is used as the default-valued
valued expression of the type. That is, no `Default()` method is generated.

```
public static readonly B Witness = W;
```

## (Co-)datatypes

Each datatype and co-datatype has a _grounding constructor_. For a `datatype`, the grounding
constructor is selected when the resolver ascertains that the datatype is nonempty. For a
`codatatype`, the selection of the grounding constructor lacks sophistication--it is just the
first of the given constructors.

If the datatype is not an auto-init type, then there's nothing more to say about its default
value. If it is an auto-init type, then the following explanations apply.

The default value of a (co-)datatype is this grounding constructor, called with values
for its parameters:

    DT<TT>.create_GroundingCtor(E, ...)

This value is produced by the `Default(...)` method emitted by the compiler into the type's
companion class:

```
public static DT<TT> Default(T e, ...) {
  return create_GroundingCtor(E, ...);
}
```

The parameters to this `Default` method are the default values for each of the type parameters
used by the grounding constructor.

If the (co-)datatype has no type parameters (note: that is, no type parameters at all--the
"used parameters" are not involved here), then the default value is pre-computed and reused:

```
private readonly DT _Default = create_GroundingCtor();
public static DT Default() {
  return _Default;
}
```

## Type parameters

If a type parameter `T` is an auto-init type parameter (that is, if it has been declared
with the `(0)` type characteristic), then the context in the target code will contain a
parameter or field named `td_T`. This is the type descriptor associated with `T`, as described
in the next section, and calling `Default()` on it yields a value of the type that `T` stands for.

Type descriptors
----------------

To obtain default values of certain type parameters, the compiler emits _run-time type descriptors_
(or just _type descriptors_ for short). A type descriptor has the ability to produce a
default value for the type that the type parameter represents.

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

The following table shows the type descriptors for the various types:

type                                             | type descriptor
-------------------------------------------------|------------------------------------------
`int`                                            | `Dafny.Helpers.INT`
`real`                                           | `Dafny.Helpers.REAL`
`bool`                                           | `Dafny.Helpers.BOOL`
`char`                                           | `Dafny.Helpers.CHAR`
bitvectors                                       | `Dafny.Helpers.{UINT8, UINT16, UINT32, UINT64, INT}`
`ORDINAL`                                        | `Dafny.Helpers.INT`
`newtype` `NT`                                   | `NT._TypeDescriptor()`
possibly-null reference type `T`                 | `Dafny.Helpers.NULL<T>()`
type parameter `T`                               | `td_T`
collection type `C<TT>`                          | `C<TT>._TypeDescriptor()`
datatype or co-datatype `D`                      | `D._TypeDescriptor(typeDescriptors, ...)`
arrow type `T`                                   | `Dafny.Helpers.NULL<T>()`
subset type `S`                                  | `D._TypeDescriptor(typeDescriptors, ...)`

## Primitive types

The type descriptors for primitive types are defined in the `Dafny.Helpers` class:

```
public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');
public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);

public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);
```

## Newtypes

The type descriptor for a `newtype` `NT` is given by the static `_TypeDescriptor` method that
the compiler emits into the companion class for `NT`.

```
private static readonly Dafny.TypeDescriptor<B> _TYPE = new Dafny.TypeDescriptor<B>(Dve);
public static Dafny.TypeDescriptor<B> _TypeDescriptor() {
  return _TYPE;
}
```

where `B` is the target type of `NT`,
and `Dve` is the default-valued expression for `NT` (`Witness` or some form of `0` or `0.0`).

## Reference types

The type descriptor for possibly-null reference types is given by the following method in
`Dafny.Helpers`:

```
public static TypeDescriptor<T> NULL<T>() where T : class {
  return new TypeDescriptor<T>(null);
}
```

## Collection types

Type descriptors for collection types are provided by the `_TypeDescriptor()` method in
the type's companion class. In each case, the quantity returned is a value computed once
and for all into a static field.

For each collection class (for example, `set<T>`), the companion class (`Set<T>` for
`set<T>`) contains the following field and method:

```
private static readonly TypeDescriptor<B> _TYPE = new Dafny.TypeDescriptor<B>(Empty);
public static TypeDescriptor<B> _TypeDescriptor() {
  return _TYPE;
}
```

where `B` denotes the target type of the collection type (`ISet<T>` for `set<T>`).

## Datatypes and co-datatypes

For any (co-)datatype `D<TT>`, the companion class for `D<TT>` declares:

```
public static Dafny.TypeDescriptor<D<TT>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T, ...) {
  return new Dafny.TypeDescriptor<D<TT>>(Default(_td_T, ...));
}
```

where the list of type parameters denoted by `T, ...` are the auto-init type parameters from `TT`.


## Subset types

The companion class of a subset type `S<TT>` contains a method `_TypeDescriptor` that returns
a type descriptor for `S<TT>`.

```
public static Dafny.TypeDescriptor<B> _TypeDescriptor(TypeDescriptor<T> td_T, ...) {
  return new Dafny.TypeDescriptor<B>(Dve);
}
```

where the list of type parameters denoted by `T, ...` consists of the auto-init type parameters from `TT`,
`B` is the target type of `S<TT>`, and
`Dve` is the default-valued expression for `S<TT>`.

If `S` has no type parameters, then the value returned by `_TypeDescriptor` is pre-computed
and reused:

```
private static readonly Dafny.TypeDescriptor<B> _TYPE = new Dafny.TypeDescriptor<B>(Dve);
public static Dafny.TypeDescriptor<B> _TypeDescriptor() {
  return _TYPE;
}
```

## Type parameters

Finally, type parameters. These are the most involved.
For each formal auto-init type parameter `T`, there is an associated type descriptor named
`td_T` (of type `Dafny.TypeDescriptor<T>`). What exactly `td_T` is depends on both the
parent declaration of `T` and the context of use.

### Type parameters of a method or function

If `T` is a type parameter of a method or function, then `td_T` is simply an additional
parameter to the method or function.

For example, a method `method M<T(0)>(x: int)` is compiled into

```
void M<T>(Dafny.TypeDescriptor<T> td_T, BigInteger x)
```

### Type parameters of a class

If `T` is a type parameter of a class, then `td_T` is a field of the target type. Its
value is given by a parameter to the target-type constructor.

For example, for

```
class Cl<T(0)> {
  constructor Init(x: int) { ... }
  ...
}
```

the target type will be

```
class Cl<T> {
  private Dafny.TypeDescriptor<T> td_T;
  public Cl(Dafny.TypeDescriptor<T> td_T) {
    this.td_T = td_T;
  }
  public void Init(x: BigInteger) { ... }
  ...
}
```

### Type parameters of a trait

To obtain type descriptors in function and method implementations that are given
in a trait, the function or method definition compiled into the companion class
takes additional parameters that represent type descriptors for the type parameters
of the trait.

### Type parameter of a class or trait used in a static method or function

In C#, the type parameters of a class are available in static methods. However,
any type descriptors of the class are stored in instance fields, since the target
types are not unique. The instance fields are not available in static methods, so
the static methods need to take the type descriptors as parameters.

For example, the class

```
class Class<A(0)> {
  static method M(x: int)
}
```

is compiled into

```
class Class<A> {
  Dafny.TypeDescriptor<A> td_A;
  ...
  static method M(Dafny.TypeDescriptor<A> td_A, BigInteger x)
}
```

### Type parameter of a `newtype` or (co-)datatype

If `T` is a type parameter of a (co-)datatype, then the target code for any function
or method takes additional parameters that represent type descriptors for the type
parameters of the enclosing type.

Type parameters and type descriptors for each type
--------------------------------------------------

In the following table, the rows show instance and static members (`const`/`function`/`method`) of
the types that support members. The type is shown with a type parameter `A(0)` (except `newtype`,
which doesn't take any type parameters). Each member is also shown with a type parameter `B(0)`
(except `const`, which doesn't take any type parameters).

For some target languages, the target type for traits does not allow implementations. In those
cases, the target type has a signature for the member and the implementation is relegated to
the companion class. This is reflected in the table by having two rows for instance members of
traits.

For each row, the "TP" column shows which of the Dafny type parameters contribute to the type
parameters in the target language, and the "TD" column shows which of the Dafny type parameters
contribute to the type descriptors in the target code.

If `A` is missing from a "TP" column, it means that either the type parameter is available from
the enclosing type or the target language doesn't support type parameters. If `A` is missing from
a "TD" column, it means that the type descriptor is available via the receiver `this`.

                                    | C#        | Java      | JavaScript | Go        |
TYPE                                | TP  | TD  | TP  | TD  | TP  | TD   | TP  | TD  |
------------------------------------|-----|-----|-----|-----|-----|------|-----|-----|
`newtype`
  instance member `<B(0)>`          | B   | B   | B   | B   |     | B    |     | B   |
  static member `<B(0)>`            | B   | B   | B   | B   |     | B    |     | B   |
`datatype<A(0)>`
  instance member `<B(0)>`          | B   | A,B | B   | A,B |     | A,B  |     | A,B |
  static member `<B(0)>`            | B   | A,B | A,B | A,B |     | A,B  |     | A,B |
`trait<A(0)>`
  instance member `<B(0)>`          | B   | B   | B   | B   |     | B    |     | B   |
  instance member `<B(0)>` rhs/body | B   | A,B | A,B | A,B |     | A,B  |     | A,B |
  static member `<B(0)>`            | B   | A,B | A,B | A,B |     | A,B  |     | A,B |
`class<A(0)>`
  instance member `<B(0)>`          | B   | B   | B   | B   |     | B    |     | B   |
  static member `<B(0)>`            | B   | A,B | A,B | A,B |     | A,B  |     | A,B |

*) type descriptors for functions don't actually seem necessary (but if functions have them,
then const's need them, too)

If the type parameters `A` and `B` does not have the `(0)` characteristic, then it is dropped
from the TD column.

This table is implemented in the `TypeArgDescriptorUse` method in the compiler.
