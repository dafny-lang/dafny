## The `JSON` module

JSON serialization and deserialization in Dafny, as described in [RFC 8259](https://datatracker.ietf.org/doc/html/rfc8259).

This library provides two APIs:

- A low-level (zero-copy) API that is efficient, verified (see [What is verified?](#what-is-verified) below for details) and allows incremental changes (re-serialization is much faster for unchanged objects), but is more cumbersome to use. This API operates on concrete syntax trees that capture details of punctuation and blanks and represent strings using unescaped, undecoded utf-8 byte sequences.

- A high-level API built on top of the previous one. This API is more convenient to use, but it is unverified and less efficient. It produces abstract datatype value trees that represent strings using Dafny's built-in `string` type.

Both APIs provides functions for serialization (JSON values to utf-8 bytes) and deserialization (utf-8 bytes to JSON values).
See the Unicode module if you need to read or produce JSON text in other encodings.

## Library usage

The tutorial in [`JSONExamples.dfy`](../../../examples/JSON/JSONExamples.dfy) shows how to import the library, call the high-level API, and use the low-level API to make localized modifications to a partial parse of a JSON AST. The main entry points are `API.Serialize` (to go from a JSON value to utf-8 bytes), and `API.Deserialize` (for the reverse operation):

<!-- %check-verify -->
```dafny
import API = Std.JSON.API
import opened Std.Unicode.UnicodeStringsWithUnicodeChar
import opened Std.JSON.Values
import opened Std.Wrappers

method Test(){
  var CITY_JS :- expect ToUTF8Checked(@"{""Cities"": [{
    ""Name"": ""Boston"",
    ""Founded"": 1630,
    ""Population"": 689386,
    ""Area (km2)"": 4584.2}]}");

  var CITY_VALUE := Object([("Cities", Array([
    Object([
      ("Name", String("Boston")),
      ("Founded", Number(Int(1630))),
      ("Population", Number(Int(689386))),
      ("Area (km2)", Number(Decimal(45842, -1)))])]))]);

  expect API.Deserialize(CITY_JS) == Success(CITY_VALUE);

  var EXPECTED :- expect ToUTF8Checked(
    @"{""Cities"":[{""Name"":""Boston"",""Founded"":1630,""Population"":689386,""Area (km2)"":45842e-1}]}"
  );

  expect API.Serialize(CITY_VALUE) == Success(EXPECTED);
}
```

## What is verified?

The low-level (zero-copy) serializer is proven sound and complete against a simple functional specification found in [`ConcreteSyntax.Spec.dfy`](ConcreteSyntax.Spec.dfy). The high-level deserializer is proven sound, but not complete, against that same specification: if a value is deserialized successfully, then re-serializing recovers the original bytestring.

### Useful submodules

Most of the contents of the `Utils/` directory are not specific to JSON. They are not sufficiently documented to be moved to the main library yet, but they provide useful functionality:

- [`Views.dfy`](Utils/Views.dfy) and [`Views.Writers.dfy`](Utils/Views.Writers.dfy) implement slices over byte strings whose bounds are representable as `int32` native integers. Adjacent slices can be merged in time `O(1)` (but see [“Caveats”](#caveats) below). To be part of the main library, it would have to be generalized to slices over any sequences and to indices represented using arbitrary integers (though Dafny does not currently have a way to have modularity over int width).

- [`Cursors.dfy`](Utils/Cursors.dfy) implements slices augmented with an inner pointer tracking a position. Functions are provided to skip over a specific byte or bytes, over bytes matching a given predicate, or over bytes recognized by a given lexer, and ghost functions are provided to express the fact that a cursor was obtained by trimming a prefix of another cursor.  Cursors are used in the implementation of the parser: after skipping over a given construct, a cursor can be split into a view (capturing the part of the string matching the construct) and a new cursor starting at the previous position, with its pointer reset to the beginning of the string. To become part of the main library, cursors would need to be generalized in the same way as views above.

- [`Lexers.dfy`](Utils/Lexers.dfy) contains a state machine that recognizes quoted strings and skips over backslash-escaped quotes.  State-machine-based lexers are used in `Cursors.dfy` to skip over complex constructs (like quoted strings), though in practice the low-level parser uses a custom function-by-method to speed up this specific case.

- [`Parsers.dfy`](Utils/Parsers.dfy) has definitions of well-formedness for parsers (stating that they must consume part of their input).  This file would have to be significantly expanded to create a composable library of parsing combinators to be useful as part of the main library.

## Caveats

- Not all parts of this library are verified. In particular, the high-level API is not verified (the most complex part of it is the string escaping code).

- The optimization used to merge contiguous slices can have poor performance in corner cases. Specifically, the function `Views.Core.Adjacent`, which checks whether two slices can be concatenated efficiently, uses Dafny's value equality, not reference equality, to check whether both slices point into the same string. The value-equality check is `O(1)` when the strings are physically equal, but may take linear time otherwise.

  The worst-case behavior happens when serializing a low-level JSON object in which the `View`s all point to (physically) different strings with equal contents. This cannot happen when modifying the result of a previous parse (in that case, all views will share the same underlying storage, and the comparison will be fast).

  This issue could be fixed by using reference equality, but doing so requires defining an external function to expose (a restricted form of) reference equality on values (exposing reference equality in general on values is not sound). A good description of the relevant technique can be found in chapter 9 of “Verasco: a Formally Verified C Static Analyzer” by Jacques-Henri Jourdan.

### Implementation notes

- The division into a low-level and a high-level API achieves two desirable outcomes:

  - Programs that modify a small part of a JSON object can be implemented much more efficiently that using a traditional JSON AST ↔ bytes API, since unmodified parts of the decoded JSON object can be reserialized very quickly.

  - Specs and proofs for the low-level API are simple because the low-level API captures all encoding details (including the amount of whitespace used), which makes serialization and deserialization uniquely determined. As a result, serialization is really the (left) inverse of deserializations.

- Most of the low-level API uses bounded integers (`int32`), so the library cannot deserialize more than 4GB of JSON text.

- To support in-place updates, the low-level API supports serializing into an existing buffer. Instead of repeatedly checking for overflows, the implementation uses saturating addition and checks for overflow only once, after writing the whole object. This optimization was inspired by Go's error-handling style, described in [Errors are values](https://go.dev/blog/errors-are-values).

- Dafny does not support floating point numbers (and the JSON spec does not mandate a specific precision), so the library uses a pair `(n, e10)` instead representing the number `n * 10^e10`.

- Workarounds for known Dafny bugs are indicated by the keyword [`BUG`](https://github.com/dafny-lang/libraries/search?q=BUG) in the sources.

## TODOs and contribution opportunities

### Verification

The high-level API is unverified. Unlike the low-level API, general JSON serialization and deserialization are not inverses of each other, because deserializing an object and re-serializing it may add or remove whitespace or change the way strings or numbers are represented (e.g. the string `"a"` may be serialized as `"\u0061"` and the number 1 as 1.0e0, 10e-1, etc.). As a result, an executable serializer is not a sufficient specification of the format. Techniques to write specifications and verify serializers and deserializers in such cases are described in e.g. [Narcissus: correct-by-construction derivation of decoders and encoders from binary formats](https://dl.acm.org/doi/abs/10.1145/3341686).

Note that it would be possible (and a great start) to show that the deserializer supports everything that the serializer may produce. This would not require a generalized specification (one that allows variation in serialization choices) of the format.

Beyond this large task, some small lemmas that should hold but were not needed by this codebase are commented out and marked as `// TODO`.

### Performance problems in the high-level API

The high-level API does string encoding and escaping as two separate passes that both construct sequences. Adding `by method` blocks and fusing these two passes would provide significant gains.

### Performance opportunities in the low-level API

The low-level API is written in the pure subset of Dafny. As a result, it creates lots of short-lived records (especially cursors, defined in [`Cursors.dfy`](Utils/Cursors.dfy)). A linear version of Dafny would be able to mutate these structures in place. A traditional reuse analysis (see e.g. Schulte & Grieskamp, “Generating Efficient Portable Code for a Strict Applicative Language”, or any of the OPAL papers) would achieve the same result. Large gains could already be achieved simply by improving the compilation of records in the C# backend (e.g. using structs for small records and removing unnecessary interfaces).

The optimization to merge contiguous string could be made to use physical equality. This would provide little gain in the typical case, but would eliminate the worst-case described in [“Caveats”](#caveats) above.

The low-level serializer does not re-serialize unchanged parts of an AST, but it still re-writes the whole object. This could be eliminated when changes to the object do not change its overall length.