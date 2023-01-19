<p></p> <!-- avoids duplicate title -->

# Strings and Characters

This document describes how the built-in Dafny types `string` and `char`
are compiled to the various supported target languages.

The `string` type is just an alias for `seq<char>`, so most of the interesting
decisions center around to represent the `char` type faithfully in each
target languages. Historically, the `char` type has acted much like the
following newtype declaration:

```dafny
newtype char = c: int | 0 <= c < 65536
```

That is, `char` really meant "UTF-16 code unit". Since Dafny `string`
values can contain invalid use of surrogates, and since this is suboptimal
for interoperating with other encodings such as UTF-8, the `--unicode-char`
option was added to enable defining `char` to mean "Unicode scalar value"
instead. This is equivalent to the following newtype declaration instead:

```dafny
newtype char = c: int | 0 <= c < 0xD800 || 0xE000 <= c < 0x11_0000
```

The selection of target language type for `char` is chosen primarily to
ensure enough bits to efficiently store and work with these ranges of values,
but also secondarily to align with the idiomatic character type where possible,
and to support outputting the expected representation when passing characters
and strings to the `print` statement.

| Language      | --unicode-char=false           | --unicode-char=true                            |
| ------------- | ------------------------------ | ---------------------------------------------- |
| C#            | `char`                         | `Dafny.Rune`                             |
| Java          | `char`                         | `int` / `dafny.CodePoint`                      |
| JavaScript    | `string` of length 1           | `_dafny.CodePoint` (`number` wrapper)          |
| Python        | `str` of length 1              | `_dafny.CodePoint` (`str` of length 1 wrapper) |
| Go            | `_dafny.Char` (`rune` wrapper) | `_dafny.CodePoint` (`rune` wrapper)            |
| C++           | `char`                         | (not supported)                                |

The various runtimes for each language support both use cases,
without any need for conditional compilation or multiple packages.
Instead some utility functions have two different implementations with similar
names but different signatures, and the corresponding compilers select
which function to reference based on the value of `--unicode-char`.
For example, most runtimes have a function named something like `SeqFromString`,
for converting from the native string type to the appropriate type for the Dafny
runtime if `--unicode-char=false`, but also a version named something like
`UnicodeSeqFromString` for the `--unicode-char=true` case. Both accept the
same input type, but the former will return something like a `Seq<Character>`
whereas the latter will return something like a `Seq<CodePoint>`.

Here are some notes to explain and justify the choices in each language
when `--unicode-char=true`:

## C#

The `Dafny.Rune` struct is a wrapper around an `int` value,
and its API guarantees that invalid values (e.g. surrogates) will be rejected on construction.
Because C# optimizes this special case of a struct with a single value,
using this in place of a direct `int` value when `--unicode-char` is enabled
does not have any runtime overhead.
We would use the standard `System.Text.Rune` struct instead,
but the `DafnyRuntime` package is built for older .NET framework versions
that don't include this type.

## Java

Java does not include a dedicated type for Unicode scalar values
and instead uses the 32-bit wide `int` primitive type in general.
The Java backend uses `int` whenever the static type of a value is known,
but boxing of some kind is necessary to cast a primitive `int` value
as a reference value when interfacing with generic code.

The solution is to define our own `CodePoint` boxing type that wraps an `int`
just as `Integer` does, but knows the true intended type more precisely
and overrides `toString()` accordingly. We also define a `TypeDescriptor`
for `UNICODE_CHAR` that uses `int` as the primitive,
unboxed type but `CodePoint` as the boxing type,
and this enables using the optimized `dafny.Array` class to store a
sequence of code points in an `int[]` instead of in a `CodePoint[]`.

## JavaScript / Python / Go

In all three of these runtimes, the `_dafny.CodePoint` type is a wrapper
around a reasonable built-in type for code points.
Note that in Go, the underlying `rune` type allows surrogate values,
and hence can be used whether `--unicode-char` is enabled or not.

## C++

The C++ `char` type is unfortunately only 8 bits wide, and hence
is not an adequate choice for arbitrary UTF-16 code units.
Addressing this and supporting the 21-bit range of Unicode scalar values
is deferred for now, as it will require pulling in additional libraries
to support printing to standard out in order to implement the `print` statement.

# Printing strings and characters

Although `string` is treated as a pure type alias within the core semantics
of Dafny, it is highly beneficial to `print` a string value as `Hello`
rather than `['H', 'e', 'l', 'l', 'o']`. With `--unicode-char=false`,
the various runtimes make best effort attempts
to identify which sequence values contain character values and hence should be
printed as strings. This means this behavior depends on how easy it is
to track this type information at runtime, and hence is not consistent
between backends.

With `--unicode-char=true`, however, this is simplified
and consistent across backends: a value is only printed as a string if
its static type is known to be `seq<char>`. This means that when using some
more generic datatypes, string values will be printed as sequence values:
printing an `Option<string>` value for example.

This is generally implemented by including a function named something similar
to `ToVerbatimString` on the sequence type in each runtime. This is only
invoked in generated code when the sequence is known to be a `seq<char>`,
and hence the runtimes are free to cast as needed to treat the values as
strings.

`--unicode-char` also changes how character values are printed by the
`print` statement: `'D'` will print as `D` when `--unicode-char=false`.
but `'D'` when `--unicode-char=true`.


# String and character literals

The simplest way to compile literals would be to materialize them as
equivalent sequence displays of code point values, un-escaping escape sequences
as needed. In other words, compiling a Dafny `"Hello"` string literal
to something like `Seq(72, 101, 108, 108, 111)`.
This would be a substantial hit to the readability of the compiled code,
however, making it harder for Dafny users and contributors to debug issues:
string literals are often helpful landmarks for orienting oneself
when trying to understand the compiled code. Therefore,
character and string literals are still translated to literals in the target
language where possible.
The `Util.MightContainNonAsciiCharacters` method is used to conservatively
identify string and character literals that should use the more general
approach using raw code point values instead.
