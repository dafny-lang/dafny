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
Primitive types like `bool`, `u8`, `i8`, `u16`... but also any references `& T`, `&mut T`, `*const T`, `*mut T` or structs of these types have copy semantics.
* *Move semantics* or *owned semantics* indicate that once a variable or a field is used without borrowing, it can no longer be used afterwards. These are the semantics that allow Rust to forget the garbage collector, by cleaning up resources Rust can statically determine they are not longer used.
Move semantics are the default for any type that does not implement the `Copy` trait.

Dafny has only Copy semantics, which as said offer a straight encoding for primitive types and reference types.
However, immutable types and datatypes are a bit harder, because variables containing them would have
move semantics by default. Fortunately, there exist a method `Cloneable::clone(&self)` that borrows an object of a struct or enum that implements the trait `Clone` and can create a duplicate. That method is a no-op for types implementing the `Copy` trait.

Hence, whenever a variable with move semantics (borrowed or owned) is used in a place that expects an owned value (such as an addition), Dafny inserts a `.Clone()` call in Rust so that the result can be used independently of the variable. Moreover, to pass a variable to any function, it must be either borrowed (prefixed with `&`) or cloned, unless Dafny could theoretically determine it's the last occurrence of this variable.

For maximum flexibility, Dafny follows these rules to encode types in Rust:
- Function parameters always take primitive types without borrowing them (`bool`, `u32`, etc.) 
- Function parameters always borrow variables of other types (`DafnyString`, structs, etc.), because
  borrowing is always cheaper than cloning for non-Copy types.  
  Open question: There are at least two more possible alternatives
  - We could actually have parameters be always owned, which require `.clone()` also to be used at the call site
  - We could have parameter attributes like `{:rc_owned true}` so that users can choose which API to precisely give to their functions.
- Functions always return an owned type, otherwise we would need to have an automated theory about lifetimes of returned borrowed references, which Dafny does not support yet. Moreover, borrowing a variable makes its lifetime not `'static`, so it's not possible to use that trait.
- `& T` and `&mut T` annotations only appear at the top-level of types, never nested.
- Classes types are encoded in reference-counted pointers by default, but there is a command-line flag `--raw-pointers` that encode class type into an equivalent of a raw pointer, in which case a deallocation statement will have to be made available.

|-------------------------------|-----------------------------|
|  Dafny type                   |   Rust type                 |
|-------------------------------|-----------------------------|
| `bool`                        | `bool`                      |
| `int`                         | `DafnyInt` (wrapper around `Rc<num::BigInt>`)   |
| `int64`                       | `i64`                       |
| `int32`                       | `i32`                       |
| `int16`                       | `i16`                       |
| `int8`                        | `i8`                        |
| `char`                        | `char` OR `u16` (`--unicode-chars=false`)  |
| `bitvector`                   | appropriate `u8` ... `u128` type  |
| `ORDINAL`                     | `DafnyInt` - TODO           |
| `real`                        | `num::BigRational` (will move to DafnyRational) |
|                               | `f64`                       |
| `string`                      | `Sequence<DafnyChar>`       |
|                               | or `Sequence<DafnyCharUTF16>`  |
| datatype, codatatype `D`      | `Rc<D>`                     |
|                               | or `D` with the option `{:rust_rc false}` |
| subset type                   | same as base type           |
| `newtype T = u: U`            | `struct T(U)`               |
|                               | or optimized to `u8`..`i128`|
| `(T1, T2...)`                 | `(T1, T2...)` except for tuple of size 13 or more which use `_System.TupleXXX` because Rust has limitations             |
| `seq<T>`                      | `Sequence<T: DafnyType>` (*)|
| `set<T>`, `iset<T>`           | `Set<T: DafnyTypeEq>` (*)      |
| `multiset<T>`                 | `MultiSet<T: DafnyTypeEq>` (*) |
| `map<T,U>`, `imap<T,U>`       | `Map<T: DafnyTypeEq, U: DafnyTypeEq>` (*) |
| function (arrow) types        | `Rc<dyn Fn(...) -> ...>`    |

## Encoding of classes and arrays (default)
This version compiles classes to reference counting, which roughly uses
the following definition
```rs
pub struct Object<T: ?Sized>(pub Option<Rc<UnsafeCell<T>>>);
```

|-------------------------------|-----------------------------|
|  Dafny type                   |   Rust type                 |
|-------------------------------|-----------------------------|
| `C`, `C?` (for class, iterator C) | `Object<C>`         (*) |
| (trait) `T`                   | (trait) `Object<dyn T>` (*) |
| `array<T>`                    | `Object<[T]>`           (*) |
| `array2<T>`                   | `Object<array2<T>>`  (*)(*) |
| `c.x` if `c: C`               | `rd!(c).x`              (*) |
| `c.x := 2` if `c: C`          | `md!(c).x = 2`          (*) |
| `a[0]` if `a: array<T>`       | `rd!(a)[0]`             (*) |
| `a[1] := 2` if  `a: array<T>` | `md!(a)[1] = 2`         (*) |


## Encoding of classes and arrays with the option --raw-pointers
The option `--raw-pointers` ensures that classes only have 8 bytes pointers,
and array only have 8 bytes pointers + information about the length,
and point to raw memory. Therefore, pointers have copy semantics and
no call to any clone method needs to be made.
However, since pointer comparison in Rust normally compares vtables,
which is brittle, Dafny use its own pointer types which are wrappers:
```rs
pub struct Ptr<T: ?Sized>(pub Option<NonNull<UnsafeCell<T>>>);
```

|-------------------------------|-----------------------------|
|  Dafny type                   |   Rust type                 |
|-------------------------------|-----------------------------|
| `C`, `C?` (for class, iterator C) | `Ptr<C>`            (*) |
| (trait) `T`                   | (trait) `Ptr<dyn T>`    (*) |
| `array<T>`                    | `Ptr<[T]>`              (*) |
| `array2<T>`                   | `Ptr<array2<T>>`    (*) (*) |
| `c.x` if `c: C`               | `read!(c).x`            (*) |
| `c.x := 2` if `c: C`          | `modify!(c).x = 2`      (*) |
| `a[0]` if `a: array<T>`       | `read!(a)[0]`           (*) |
| `a[1] := 2` if  `a: array<T>` | `modify!(a)[1] = 2`     (*) |

(*) Defined in the Dafny runtime

# Externs

You can provide additional `*.rs` files to `dafny translate`, `dafny build` and even `dafny run` (via the `--input` option)
All the elements imported from the Rust files are going to be available from the generated code via the module `_dafny_externs` that imports everything.

The best way to see what you have to implement as an extern is to compile your code without it. You'll see that it will be necessary for the module `_dafny_extern` to use open a certain module, which you'd put in a file `external.rs` and pass it for compilation.

When using simple 1-argument externs, the compilation follows Dafny conventions:
* Static methods are static instance methods of a `pub struct _default {}` which is defined in the module itself, or must be defined externally if all static methods are labelled as externs.
* Methods or functions with an extern attribute with 2 arguments are interpreted as follow: The first argument is a module name, and all the "." are rewritten to "::" to follow Rust's syntax. The second argument is the name of a static `pub fn` of that module.

Let's assume you provide an additional input file `external.rs` with the following content:
```
pub mod rust {
  pub mod module {
    fn outsideMethod()
  }
}
pub mod Test {
  pub struct _default {}
  impl _default {
    pub fn extern_y() {
    }
  }
}
```
Assuming that your Dafny program looks like:

```

module Test {
  method {:extern "rust.module", "externalMethod"} outsideMethod()
  method {:extern "extern_y"} dafny_y();
}
method Main() {
  Test.outsideMethod();
  Test.dafny_y();
}
```

Dafny will generate the following for you:

```
pub mod external;         // from the additional external.rs input file

pub mod _dafny_externs {  // from the additional external.rs input file
  import opened external::*;
}
pub mod Test {
  pub use super::_dafny_externs::Test::*; // Imports the _default
}
fn main() {
  crate::rust::module::externalMethod();
  super::Test::_default::extern_y();
}
```

Note: 
Note that if the extern module name contains a space, any dot after the space is not replaced by `::`.