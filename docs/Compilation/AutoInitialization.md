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
variable to be initialized with _some_ value of the variable's type.[^fn-determinism]
To accomplish this, the compiler needs to have the ability to emit an expression that
produces a value of a given type. This is possible for many, but not all, types.

This document describes for which types the compiler can produce initializing
expressions and the mechanism used for doing so.

[^fn-determinism]: The command-line option `/definiteAssignment:3` tells Dafny to
    instead generate an error if a variable is not assigned by the program.

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
`char`                          | `char`
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
same as the target type, and in other cases there is no companion class at all.

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

Types can have type parameters. Each _formal_ type parameter is compiled into a corresponding
formal type parameter in the target language, with one exception. The exception is for
subset types, whose type parameters are expanded as part of the base type. Each _actual_
type argument is compiled to that type's target type.

Because target types are not unique, the type arguments passed as required by the target
language do not carry all information that is needed about the type at run time.
Therefore, the Dafny compiler augments the target language's type parameters by a
system of _type descriptors_. These are described in a section below.

Type descriptors are passed only for type parameters that bear the Dafny type characteristic
`(0)`. Such type parameters are called _auto-init type parameters_.

For inductive datatypes, the compiler uses one more notion of types, namely the
_used type parameters_. This refers to those type parameters that play a role in the
creation of a value of the datatype's "root constructor", explained below.
TODO: These "used type parameters" were needed long ago, but things have changed in
the language; can they now be removed?

Auto-init types
---------------

A type is called an _auto-init type_ if it is legal for a program to use a variable of
that type before the variable has been initialized.

For example, `char` is an auto-init type. Therefore, the following is a legal program
snippet:

    var ch: char;
    print ch, "\n";

A compiler is permitted to assign _any_ value to `ch`, so long as that value is of
type `char`. In fact, the compiler is free to emit code that chooses a different
initial value each time this program snippet is encountered at run time. In other words,
the language allows the selection of the values to be nondeterministic.

The purpose of this document is to describe how the compiler (in particular, the
Dafny-to-C# compiler in `Compiler-CSharp.cs`, though the other targets are similar) implements
the auto-init feature. It will be convenient (and, for this particular compiler, accurate)
to speak of each type as having a _default value_. However, please note that this
terminology is specific to an implementation of a compiler--the Dafny _language_ itself
does not have a notion of specific a "default value" of any type, not even for auto-init
types.

Default-valued expressions
--------------------------

To fabricate default values, the compiler uses a combination of _default-valued expressions_
and _type descriptors_. This section describes the former; the next section describes the
latter.

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
type parameter `T`                               | `td_T.Default()`
collection type `C`                              | `C.Empty`
datatype or co-datatype `D`                      | `D.Default(E, ...)`
`TT ~> U`                                        | `null`
`TT --> U`                                       | `null`
subset type without `witness` clause             | same as for base type
subset type `S` with `witness` clause            | `S.Witness`

Other types do not have default-valued expressions.
Here are some additional explanations of the table:

The `witness` clause, if any, of a `newtype` or subset type gets recorded in a static field of the
companion class:

```
public static readonly B Witness = E;
```

where `B` is type's target type and `E` is the expression given in the `witness` clause.
No such `Witness` field is emitted if either there is no `witness` clause or it is given as
a `ghost witness` clause.

If a type parameter `T` is an auto-init type parameter (that is, if it has been declared
with the `(0)` type characteristic), then the context in the target code will contain a
parameter or field named `td_T`. This is the type descriptor associated with `T`, as described
below, and calling `Default()` on it yields a value of the type that `T` stands for.

Each datatype and co-datatype has a _root constructor_. For a `datatype`, the root constructor
is selected when the resolver ascertains that the datatype is nonempty. For a `codatatype`,
the selection of the root constructor lacks sophistication--it is just the first of the given
constructors. The default value of a (co-)datatype is this root constructor, called with values
for its parameters:

    D.create_RootCtor(E, ...)

This value is produced by the `Default(...)` method emitted by the compiler into the type's
companion class:

```
public static DT Default(T e, ...) {
  return create_RootCtor(e, ...);
}
```

where `DT` is the target type of the (co-)datatype.
TODO: What are the parameters to this `Default(...)` method? I think it's only a subset of the
parameters passed to the root constructor, right? Only those parameters that can be constructed
only through auto-init type parameters are needed. This affects the first sentence of the next paragraph.

type parameter `T`                               | `td_T`
collection type `C`                              | `C._TypeDescriptor()`
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
the type's companion class. In each case, the return returned is a value computed once
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

TODO: What about "used type parameters"?

## Subset types

The companion class of a subset type `S<TT>` contains a method `_TypeDescriptor` that returns
a type descriptor for `S<TT>`.

```
public static Dafny.TypeDescriptor<B> _TypeDescriptor(TypeDescriptor<T> td_T, ...) {
  return new Dafny.TypeDescriptor<B>(Dve);
}
```

where the list of type parameters denoted by `T, ...` are the auto-init type parameters from `TT`,
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

TODO: If `T` is used as the type of an undeclared local variable in the method of a
trait, then does this really work? I guess this can work if the target interface
has a `td_T` getter that's computed appropriately in the class.

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

If `T` is a type parameter of a (co-)datatype, then...
TODO: See the concern about traits immediately above. Should auto-init type parameters
be disallowed in (co-)datatypes? Is that also a reasonable solution for traits?



---------------------------------------
Notes
---------------------------------------

* List<TypeParameter>
  CombineTypeParameters(MemberDecl member, bool forCompanionClass = false)

  Return ta.Formal for either of the calls below.

  + as argument to CreateFunction (3x), for ConstantField in CompileClassMembers
  + as argument to CreateFunction, in CompileFunction
  + as argument to CreateMethod, in CompileMethod

* List<TypeArgumentInstantiation>
  CombineTypeArgumentsForCompanionClass(MemberDecl member, List<Type> typeArgsEnclosingClass, List<Type> typeArgsMember)

  For C#, member parameters only.
  For non-C#, class parameters whenever any of:
  - any static member
  - instance member in newtype
  - instance const/function/method in trait with rhs/body/body

  + used by EmitCallToInheritedConstRHS, for both TP and TD
  + used by EmitCallToInheritedFunction, for both TP and TD
  + used by EmitCallToInheritedMethod, for both TP and TD

* List<TypeArgumentInstantiation>
  CombineTypeArguments(MemberDecl member, List<Type> typeArgsEnclosingClass, List<Type> typeArgsMember)

  For C#, member parameters only.
  For non-C#, class parameters whenever any of:
  - any static member
  - instance member in newtype

  + used by TrCallStmt, for both TP and TD
  + used 4x by TrExpr (case MemberSelectExpr), which calls EmitMemberSelect
  + used by CompileFunctionCallExpr, for both TP and TD


------------------------------------

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
  instance member `<B(0)>`          | B   | B   | B   | B   |     | B    |     | A,B |
  instance member `<B(0)>` rhs/body | B   | A,B | B   | A,B |     | A,B  |     | A,B |
  static member `<B(0)>`            | B   | A,B | A,B | A,B |     | A,B  |     | A,B |

`class<A(0)>`
  instance member `<B(0)>`          | B   | B   | B   | B   |     | B    |     | B   |
  static member `<B(0)>`            | B   | A,B | A,B | A,B |     | A,B  |     | A,B |

*) type descriptors for functions don't actually seem necessary (but if functions have them,
then const's need them, too)

If the type parameters `A` and `B` does not have the `(0)` characteristic, then it is dropped
from the TD column.

This table is implemented in the `TypeArgDescUse` method in the compiler.
