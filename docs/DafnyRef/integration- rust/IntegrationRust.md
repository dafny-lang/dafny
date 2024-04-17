---
title: Integrating Dafny and Rust code
---

## THIS FILE IS A WORK IN PROGRESS, IT CAN BE MODIFIED AT ANY TIME WITHOUT NOTICE
** The Dafny-to-Rust compiler is not an officially supported backend yet**

The `dafny build` and `dafny run` currently translate a entry Dafny program `<program>.dfy`
or project file like `program/dfyconfig.toml` into the following architecture,
where the program depends on the Dafny runtime crate explicitly.
```
program-rust/   // Can be changed with --output:
  runtime/
    src/
      lib.rs    // The Dafny runtime
    cargo.lock
    cargo.toml
  src/
    program.rs  // The generated program
  cargo.lock
  cargo.toml
```

With `dafny translate`, only `program-rust/src/program.rs` is emitted.

## **Matching Dafny and Rust types**

It's worth recalling that Rust has two semantics for variables:

* *Copy semantics* are the one everyone used to `C#`, `Java`, `JavaScript`, `Go` understand.
At run-time, it means the actual bits of memory are copied from one location to the other.
Primitive types like `bool`, `u8`, `i8`, `u16`... but also any references `& T`, `&mut T`, `*const T` or `*mut T` have copy semantics.
* *Move semantics* or *owned semantics* indicate that once a variable or a field is used without borrowing, it can no longer be used afterwards. These are the semantics that allow Rust to forget the garbage collector, by cleaning up resources Rust can statically determine they are not longer used.
Move semantics are the default for any type that does not implement the `Copy` trait.

Dafny has only Copy semantics, which as said offer a straight encoding for primitive types and reference types.
However, immutable types and datatypes are a bit harder, because variables containing them would have
move semantics by default. Fortunately, there exist a method `Cloneable::clone(&self)` that borrows an object of a struct or enum that implements the trait `Clone` and can create a duplicate. That method is a no-op for types implementing the `Copy` trait.

Hence, whenever a variable with move semantics (borrowed or owned) is used in a place that expects an owned value (such as an addition), Dafny inserts a `.Clone()` call in Rust so that the result can be used independently of the variable. Moreover, to pass a variable to any function, it must be either borrowed (prefixed with `&`) or cloned, unless Dafny could theoretically determine it's the last occurrence of this variable.

For maximum flexibility, Dafny follows these rules to encode types in Rust:
- Function parameters always take primitive types without borrowing them (`bool`, `u32`, etc.) 
- Function parameters always borrows variables of other types (`DafnyString`, structs, etc.), because
  borrowing is always cheaper than cloning for non-Copy types.  
  Open question: There are at least two more possible alternatives
  - We could actually have parameters be always owned, which require `.clone()` also to be used at the call site
  - We could have parameter attributes like `{:rc_owned true}` so that users can choose which API to precisely give to their functions.
- Functions always return an owned type, otherwise we would need to have an automated theory about lifetimes of returned borrowed references, which Dafny does not support. Moreover, borrowing a variable makes its lifetime not `'static`, so it's not possible to use that trait.
- `& T` and `&mut T` annotations only appear at the top-level of types, never nested.
- Classes types are encoded in raw pointers, and a deallocation statement will be made available.

|-------------------------------|-----------------------------|
|  Dafny type                   |   Rust type                 |
|-------------------------------|-----------------------------|
| `bool`                        | `bool`                      |
| `int`                         | `DafnyInt` (wrapper around `Rc<num::BigInt>`)   |
| `int64`                       | `i64`                       |
| `int32`                       | `i32`                       |
| `int16`                       | `i16`                       |
| `int8`                        | `i8`                        |
| `char`                        | `char` OR `u16`             |
| `bitvector`                   | appropriate `u8` ... `u128` type  |
| `ORDINAL`                     | `DafnyInt` - TODO           |
| `real`                        | `num::BigRational` (will move to DafnyRational) |
|                               | `f64`                       |
| `string`                      | `Sequence<DafnyChar>`       |
|                               | or `Sequence<DafnyCharUTF16>`  |
| `C`, `C?` (for class, iterator C) | `*mut C`                |
| (trait) `T`                   | (trait) `*mut dyn T`        |
| datatype, codatatype `D`      | `Rc<D>`                     |
|                               | or `D` with the option `{:rust_rc false}` |
| subset type                   | same as base type           |
| `newtype T = u: U`            | `struct T(U)`               |
|                               | or optimized to `u8`..`i128`|
| `(T1, T2...)`                 | `(T1, T2...)`               |
| `array<T>`                    | `*mut [T]`                  |
| `array2<T>`                   | `*mut array2<T>`            |
| `seq<T>`                      | `Sequence<T: DafnyType>` (*)|
| `set<T>`, `iset<T>`           | `Set<T: DafnyTypeEq>` (*)      |
| `multiset<T>`                 | `MultiSet<T: DafnyTypeEq>` (*) |
| `map<T,U>`, `imap<T,U>`       | `Map<T: DafnyTypeEq, U: DafnyTypeEq>` (*) |
| function (arrow) types        | `Rc<dyn Fn(...) -> ...>`    |

(*) Defined in the Dafny runtime

