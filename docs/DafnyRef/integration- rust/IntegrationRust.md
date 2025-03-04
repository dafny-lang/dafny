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
- Class types are encoded in reference-counted pointers by default, but there is a command-line flag `--raw-pointers` that encodes class type into an equivalent of a raw pointer. The Dafny team will have to make a deallocation statement available in the future, as it is not available yet. Please weight in on [this issue](https://github.com/dafny-lang/dafny/issues/5257) if you are interested.

For each construct, the third column indicates if it's in the Dafny runtime, is native built-in in Rust, or is a Rust crate.
If runtime, it also indicates in parentheses what it is roughly equivalent to. `[[U]]` notation indicates the Rust equivalent of the Dafny type `U`.
The exact runtime types are subject to change, and code that is not Dafny-generated should not rely on those details.

For guaranteed stability, code interfacting with Dafny structures should use types and conversions from `pub mod dafny_runtime_conversions`, such as `::dafny_runtime::dafny_runtime_conversions::DafnySequence<T>` and `::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(array: &Vec<X>, elem_converter: fn(&X) -> T) -> DafnySequence<T>` for example.

|  Dafny type                   |   Rust type                 | Defined in       |
|-------------------------------|-----------------------------|------------------|
| `bool`                        | `bool`                      | Native           |
| `int`                         | `DafnyInt`                  | Runtime (`Rc<num::BigInt>`) |
| `int64`                       | `i64`                       | Native           |
| `int32`                       | `i32`                       | Native           |
| `int16`                       | `i16`                       | Native           |
| `int8`                        | `i8`                        | Native           |
| `char`                        | `DafnyChar`                 | Runtime (`char`) |
| `char` (`--unicode-chars=false`)| `DafnyCharUTF16`          | Runtime (`u16`)  |
| `bv8` ... `bv128`             | `u8` ... `u128`             | Native           |
| `type T = u: U | <range>`     | `[[U]]`                     | Native           |
| `newtype T = u: U | range`    | `struct T([[U]])`           | Native           |
| `newtype T = u: int | <range>`| `u8` ... `i128`             | Native           |
| `ORDINAL`                     | N/A                         | TODO             |
| `real`                        | Partially supported         | TODO             |
| `seq<T>`                      | `Sequence<[[T]]>           `| Runtime |
| `set<T>`, `iset<T>`           | `Set<[[T]]>`                | Runtime |
| `multiset<T>`                 | `Multiset<[[T]]>`           | Runtime |
| `map<T>`, `imap<T>`           | `Map<[[T]]>`                | Runtime |
| `string`                      | `DafnyString`           | Runtime (`Sequence<DafnyCharUTF16>`) |
| `string` (`--unicode-chars=false`)| `DafnyStringUTF16`      | Runtime (`Sequence<DafnyCharUTF16>`) |
| (co)datatype `D`              | `std::rc::Rc<D>`            | Native wrapped struct |
| (co)datatype `D` with attribute `{:rust_rc false}` | `D`    | Native struct    |
| `(T1, T2...)`  (Up to size 12)| `(T1, T2...)`               | Native           |
| `(T1, T2..., TN)` (13<=N<=20) | `_System.TupleN`            | Runtime because Rust limitations |
| `A -> B`                      | `Rc<dyn Fn([[A]]) -> [[B]]>`| Native (note: arguments always borrowed) |

## Encoding of classes and arrays (default)
By default, Dafny uses reference counting to compile class and array references.

|  Dafny type                   |   Rust type             | Defined in       |
|-------------------------------|-------------------------|------------------|
| `C`, `C?` (for class, iterator C) | `Object<C>`         | Runtime (`Option<Rc<UnsafeCell<C>>>`) |
| (trait) `T`                   | (trait) `Object<dyn T>` | Runtime (`Option<Rc<UnsafeCell<dyn T>>>`) |
| `array<T>`                    | `Object<[T]>`           | Runtime (`Option<Rc<UnsafeCell<[T]>>>`) |
| `array2<T>`                   | `Object<array2<T>>`     | Runtime (`struct array2 {length0: usize, length1: usize, data: Box<[Box<[T]>]>}`)     |
| `array3<T>` ... `array16<T>`  | `Object<array3<T>>` ... `Object<array16<T>>` | Runtime (`struct arrayN {length0: usize, ... lengthN-1: usize, data: Box<[...Box<[T]>...]>}`)     |
| `c.x` if `c: C`               | `rd!(c).x`              | Runtime         |
| `c.x := 2` if `c: C`          | `md!(c).x = 2`          | Runtime         |
| `a[0]` if `a: array<T>`       | `rd!(a)[0]`             | Runtime         |
| `a[1] := 2` if  `a: array<T>` | `md!(a)[1] = 2`         | Runtime         |


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

|  Dafny type                   |   Rust type             | Defined in       |
|-------------------------------|-------------------------|------------------|
| `C`, `C?` (for class, iterator C) | `Ptr<C>`            | Runtime (`Option<NonNull<UnsafeCell<C>>>`) |
| (trait) `T`                   | (trait) `Ptr<dyn T>`    | Runtime (`Option<NonNull<UnsafeCell<dyn T>>>`) |
| `array<T>`                    | `Ptr<[T]>`              | Runtime (`Option<NonNull<UnsafeCell<[T]>>>`) |
| `array2<T>`                   | `Ptr<array2<T>>`        | Runtime (`struct array2 {length0: usize, length1: usize, data: Box<[Box<[T]>]>}`)     |
| `array3<T>` ... `array16<T>`  | `Ptr<array3<T>>` ... `Ptr<array16<T>>` | Runtime (`struct arrayN {length0: usize, ... lengthN-1: usize, data: Box<[...Box<[T]>...]>}`)     |
| `c.x` if `c: C`               | `read!(c).x`            | Runtime         |
| `c.x := 2` if `c: C`          | `modify!(c).x = 2`      | Runtime         |
| `a[0]` if `a: array<T>`       | `read!(a)[0]`           | Runtime         |
| `a[1] := 2` if  `a: array<T>` | `modify!(a)[1] = 2`     | Runtime         |

# Externs

You can provide additional `*.rs` files to `dafny translate`, `dafny build` and even `dafny run` (via the `--input` option). We recommend giving each extern file a suffix `_extern.rs` to avoid name collisions. To understand how to fill these extern files, consider the corresponding section.

## Partial extern modules

If a module is defined in Dafny, but has types defined as externs, make sure you mark your module with `{:extern <name>}` where `<name>` is typically the module name.
Then, in a file `<name>_extern.rs` that you include with the build, put the following code:

```
pub mod <name> {
}
```

and you've just got started with a skeleton to fill implementations for Dafny axioms.

## Externally implemented traits and classes

You can define an extern Dafny trait in your extern rust files. Consider the following Dafny general trait declaration:

```
trait {:extern} ForeignTrait {}
```

To implement this in your extern file, use the following template:
```
  pub trait ForeignTrait {
    fn _clone(&self) -> Box<dyn ForeignTrait>;
  }

  impl Clone for Box<dyn ForeignTrait> {
    fn clone(&self) -> Self {
      self._clone()
    }
  }

  impl ::dafny_runtime::DafnyPrint for Box<dyn ForeignTrait> {
    fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        write!(f, "object")
    }
  }
```

For classes, make sure all your mutable fields are wrapped in a `::dafny_runtime::Field` so that it's always possible to share the reference.

## Other externs

The best way to see what you have to implement as an extern Rust file is to compile your code with extern attributes and adding an external Rust file. For extra methods or static methods, you would then define an additional implementation in the extern Rust file. For other class or struct types, you just need to define them without any `mod` wrapper, or using the module structure as defined in the `{:extern}` attribute.

When using simple 1-argument externs, the compilation follows Dafny conventions: static methods are static instance methods of a `pub struct _default {}` which is defined in the module itself, or must be defined externally if all static methods are labelled as externs.
When using 2-argument extern methods or functions, the compilation follows Rust convention: The first argument is a path of Rust module names separated by `::` (or `.` for cross-compilation with e.g. the Java compiler). The second argument is the name of a static `pub fn` of that module.

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

As of today, Dafny will generate the following for you (internal names not guaranteed):

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

# Tests

* Methods with the `{:test}` attribute will produce an equivalent `#[test]` method that can be run via `cargo test` on the code produced by `dafny build`.
* Modules with the `{:rust_cfg_test}` attribute will have the attribute `#[cfg(test)]` when translated to Rust.