/** 
 This library offers two APIs: a high-level one (giving abstract value trees
 with no concrete syntactic details) and a low-level one (including all
 information about blanks, separator positions, character escapes, etc.).
 */

/** High-level API (JSON values) */
@Options("-functionSyntax:4")
module AbstractSyntax {
  import Std.JSON.API
  import opened Std.JSON.Values
  import opened Std.Wrappers
  import opened Std.Unicode.UnicodeStringsWithUnicodeChar

  /** 
   The high-level API works with fairly simple datatype values that contain 
   native Dafny strings. 
   */
  @Test
  @ResourceLimit("100e6")
  method Test() {

    /**
     Use `API.Deserialize` to deserialize a byte string.
     For example, here is how to decode the JSON test `"[true]"`. (We need to
     convert from Dafny's native strings to byte strings because Dafny does not
     have syntax for byte strings; in a real application, we would be reading and
     writing raw bytes directly from disk or from the network instead).
     */
    var SIMPLE_JS :- expect ToUTF8Checked("[true]");
    var SIMPLE_VALUE := Array([Bool(true)]);
    expect API.Deserialize(SIMPLE_JS) == Success(SIMPLE_VALUE);

    /** 
     Here is a larger object, written using a verbatim string (with `@"`).
     In verbatim strings `""` represents a single double-quote character): 
     */
    var CITIES_JS :- expect ToUTF8Checked(@"{
        ""Cities"": [
          {
            ""Name"": ""Boston"",
            ""Founded"": 1630,
            ""Population"": 689386,
            ""Area (km2)"": 4584.2
          }, {
            ""Name"": ""Rome"",
            ""Founded"": -753,
            ""Population"": 2.873e6,
            ""Area (km2)"": 1285
          }, {
            ""Name"": ""Paris"",
            ""Founded"": null,
            ""Population"": 2.161e6,
            ""Area (km2)"": 2383.5
          }
        ]
      }");
    var CITIES_VALUE :=
      Object([
               ("Cities", Array([
                Object([
                ("Name", String("Boston")),
                ("Founded", Number(Int(1630))),
                ("Population", Number(Int(689386))),
                ("Area (km2)", Number(Decimal(45842, -1)))
                ]),
                Object([
                ("Name", String("Rome")),
                ("Founded", Number(Int(-753))),
                ("Population", Number(Decimal(2873, 3))),
                ("Area (km2)", Number(Int(1285)))
                ]),
                Object([
                ("Name", String("Paris")),
                ("Founded", Null),
                ("Population", Number(Decimal(2161, 3))),
                ("Area (km2)", Number(Decimal(23835, -1)))
                ])
                ]))
             ]);
    expect API.Deserialize(CITIES_JS) == Success(CITIES_VALUE);

    /** 
     Serialization works similarly, with `API.Serialize`. For this first example
     the generated string matches what we started with exactly:
     */
    expect API.Serialize(SIMPLE_VALUE) == Success(SIMPLE_JS);

    /** 
     For more complex object, the generated layout may not be exactly the same; 
     note in particular how the representation of numbers and the whitespace have changed.
    */
    var EXPECTED :- expect ToUTF8Checked(
      @"{""Cities"":[{""Name"":""Boston"",""Founded"":1630,""Population"":689386,""Area (km2)"":45842e-1},{""Name"":""Rome"",""Founded"":-753,""Population"":2873e3,""Area (km2)"":1285},{""Name"":""Paris"",""Founded"":null,""Population"":2161e3,""Area (km2)"":23835e-1}]}"
    );
    expect API.Serialize(CITIES_VALUE) == Success(EXPECTED);

    /** 
     Additional methods are defined in `API.dfy` to serialize an object into an
     existing buffer or into an array. Below is the smaller example as a sanity check:
     */
    var CITY_JS :- expect ToUTF8Checked(@"{""Cities"": [{
      ""Name"": ""Boston"",
      ""Founded"": 1630,
      ""Population"": 689386,
      ""Area (km2)"": 4584.2}]}");

    var CITY_VALUE :=
      Object([("Cities", Array([
               Object([
               ("Name", String("Boston")),
               ("Founded", Number(Int(1630))),
               ("Population", Number(Int(689386))),
               ("Area (km2)", Number(Decimal(45842, -1)))])]))]);

    expect API.Deserialize(CITY_JS) == Success(CITY_VALUE);

    var EXPECTED' :- expect ToUTF8Checked(
      @"{""Cities"":[{""Name"":""Boston"",""Founded"":1630,""Population"":689386,""Area (km2)"":45842e-1}]}"
    );

    expect API.Serialize(CITY_VALUE) == Success(EXPECTED');
  }
}

/** Low-level API (concrete syntax) */

/** 
 If you care about low-level performance, or about preserving existing
 formatting as much as possible, you may prefer to use the lower-level API:
 */
@Options("-functionSyntax:4")
module ConcreteSyntax {
  import Std.JSON.ZeroCopy.API
  import opened Std.Unicode.UnicodeStringsWithUnicodeChar
  import opened Std.JSON.Grammar
  import opened Std.Wrappers
  import Std.Collections.Seq

  /** 
   The low-level API works with ASTs that record all details of formatting and
   encoding: each node contains pointers to parts of a string, such that
   concatenating the fields of all nodes reconstructs the serialized value.
  */
  @Test
  @ResourceLimit("100e6")
  method Test() {

    /** 
     The low-level API exposes the same functions and methods as the high-level
     one, but the type that they consume and produce is `Grammar.JSON` (defined
     in `Grammar.dfy` as a `Grammar.Value` surrounded by optional whitespace)
     instead of `Values.JSON` (defined in `Values.dfy`). Since `Grammar.JSON` contains
     all formatting information, re-serializing an object produces the original value:
     */
    var CITIES :- expect ToUTF8Checked(@"{
        ""Cities"": [
          {
            ""Name"": ""Boston"",
            ""Founded"": 1630,
            ""Population"": 689386,
            ""Area (km2)"": 4600
          }, {
            ""Name"": ""Rome"",
            ""Founded"": -753,
            ""Population"": 2.873e6,
            ""Area (km2)"": 1285
          }, {
            ""Name"": ""Paris"",
            ""Founded"": null,
            ""Population"": 2.161e6,
            ""Area (km2)"": 2383.5
          }
        ]
      }");

    var deserialized :- expect API.Deserialize(CITIES);
    expect API.Serialize(deserialized) == Success(CITIES);

    /** 
     Since the formatting is preserved, it is also possible to write
     minimally-invasive transformations over an AST. For example, let's replace
     `null` in the object above with `"Unknown"`. First, we construct a JSON 
     value for the string `"Unknown"`; this could be done by hand using 
     `View.OfBytes()`, but using `API.Deserialize` is even simpler:
    */
    var UNKNOWN_JS :- expect ToUTF8Checked(@"""Unknown""");
    var UNKNOWN :- expect API.Deserialize(UNKNOWN_JS);

    /** 
     `UNKNOWN` is of type `Grammar.JSON`, which contains optional whitespace and
     a `Grammar.Value` under the name `UNKNOWN.t`, which we can use in the
     replacement:
    */
    var without_null := deserialized.(t := ReplaceNull(deserialized.t, UNKNOWN.t));

    /** 
     Then, if we reserialize, we see that all formatting (and, in fact, all of
     the serialization work) has been reused:
    */
    var expected_js :- expect ToUTF8Checked(@"{
        ""Cities"": [
          {
            ""Name"": ""Boston"",
            ""Founded"": 1630,
            ""Population"": 689386,
            ""Area (km2)"": 4600
          }, {
            ""Name"": ""Rome"",
            ""Founded"": -753,
            ""Population"": 2.873e6,
            ""Area (km2)"": 1285
          }, {
            ""Name"": ""Paris"",
            ""Founded"": ""Unknown"",
            ""Population"": 2.161e6,
            ""Area (km2)"": 2383.5
          }
        ]
      }");
    var actual_js :- expect API.Serialize(without_null);
    expect actual_js == expected_js;
  }

  /** All that remains is to write the recursive traversal: */
  function ReplaceNull(js: Value, replacement: Value): Value {
    match js
    /** Non-recursive cases are untouched: */
    case Bool(_) => js
    case String(_) => js
    case Number(_) => js
    /** `Null` is replaced with the new `replacement` value: */
    case Null(_) => replacement
    /** 
     … and objects and arrays are traversed recursively (only the data part of is
     traversed: other fields record information about the formatting of braces,
     square brackets, and whitespace, and can thus be reused without
     modifications):
    */
    case Object(obj) =>
      Object(obj.(data := MapSuffixedSequence(obj.data, (s: Suffixed<jKeyValue, jcomma>) requires s in obj.data =>
                                                s.t.(v := ReplaceNull(s.t.v, replacement)))))
    case Array(arr) =>
      Array(arr.(data := MapSuffixedSequence(arr.data, (s: Suffixed<Value, jcomma>) requires s in arr.data =>
                                               ReplaceNull(s.t, replacement))))
  }

  /** 
   Note that well-formedness criteria on the low-level AST are enforced using
   subset types, which is why we need a bit more work to iterate over the
   sequences of key-value paris and of values in objects and arrays.
   Specifically, we need to prove that mapping over these sequences doesn't
   introduce dangling punctuation (`NoTrailingSuffix`). We package this
   reasoning into a `MapSuffixedSequence` function:
  */
  function MapSuffixedSequence<D, S>(sq: SuffixedSequence<D, S>, fn: Suffixed<D, S> --> D)
    : SuffixedSequence<D, S>
    requires forall suffixed | suffixed in sq :: fn.requires(suffixed)
  {
    // BUG(https://github.com/dafny-lang/dafny/issues/2184)
    // BUG(https://github.com/dafny-lang/dafny/issues/2690)
    var fn' := (sf: Suffixed<D, S>) requires (ghost var in_sq := sf => sf in sq; in_sq(sf)) => sf.(t := fn(sf));
    Seq.Map(fn', sq)
  }

  lemma MapSuffixedSequenceNoTrailingSuffix<D, S>(sq: SuffixedSequence<D, S>, fn: Suffixed<D, S> --> D)
    requires forall suffixed | suffixed in sq :: fn.requires(suffixed)
    ensures NoTrailingSuffix(MapSuffixedSequence<D, S>(sq, fn))
  {
    var sq' := MapSuffixedSequence<D, S>(sq, fn);
    forall idx | 0 <= idx < |sq'| ensures sq'[idx].suffix.Empty? <==> idx == |sq'| - 1 {
      calc {
        sq'[idx].suffix.Empty?;
        sq[idx].suffix.Empty?;
        idx == |sq| - 1;
        idx == |sq'| - 1;
      }
    }
  }
}
