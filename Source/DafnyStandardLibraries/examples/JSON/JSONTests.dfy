abstract module AbstractWrapper {
  import Std.Strings
  import opened Std.BoundedInts
  import opened Std.Unicode.UnicodeStringsWithUnicodeChar
  import opened Std.JSON.Errors

  type JSON

  method Deserialize(bs: bytes) returns (js: DeserializationResult<JSON>)
  method SpecSerialize(js: JSON) returns (bs: SerializationResult<bytes>)
  method Serialize(js: JSON) returns (bs: SerializationResult<bytes>)
  method Check(bs: bytes, js: JSON, bs': bytes, sbs': bytes, js': JSON)

  method TestBytestring(bs: bytes, indent: string) {
    var js  :- expect Deserialize(bs);
    // print indent, "=> ", js, "\n";
    var bs'  :- expect Serialize(js);
    // print indent, "=> ", FromUTF8Checked(bs').ToOption(), "\n";
    var sbs' :- expect SpecSerialize(js);
    // print indent, "=> ", FromUTF8Checked(sbs').ToOption(), "\n";
    var js'  :- expect Deserialize(bs');
    Check(bs, js, bs', sbs', js');
  }

  method TestString(str: string, indent: string) {
    var bs :- expect ToUTF8Checked(str);
    TestBytestring(bs, indent);
  }

  method TestStrings(vectors: seq<string>) {
    for i := 0 to |vectors| {
      var input := vectors[i];
      var idx := Strings.OfInt(i);
      var indent := seq(|idx| + 1, _ => ' ');
      // print "[", idx, "]: ", input, "\n";
      TestString(input, indent);
      // print "\n";
    }
  }
}

module ZeroCopyWrapper refines AbstractWrapper {
  import opened Std.Wrappers
  import Std.JSON.Grammar
  import Std.JSON.ZeroCopy.API
  import Std.JSON.ConcreteSyntax.Spec

  type JSON = Grammar.JSON

  method Deserialize(bs: bytes) returns (js: DeserializationResult<JSON>) {
    js := API.Deserialize(bs);
  }

  method Serialize(js: JSON) returns (bs: SerializationResult<bytes>) {
    // print "Count: ", wr.chain.Count(), "\n";
    bs := API.Serialize(js);
  }

  method SpecSerialize(js: JSON) returns (bs: SerializationResult<bytes>) {
    bs := Success(Spec.JSON(js));
  }

  method Check(bs: bytes, js: JSON, bs': bytes, sbs': bytes, js': JSON) {
    expect sbs' == bs' == bs;
    expect js' == js; // This doesn't hold in general, since the views could be different
  }
}

module AbstractSyntaxWrapper refines AbstractWrapper {
  import opened Std.Wrappers
  import Std.JSON.Grammar
  import Std.JSON.API
  import Std.JSON.Values
  import Std.JSON.Spec

  type JSON = Values.JSON

  method Deserialize(bs: bytes) returns (js: DeserializationResult<JSON>) {
    js := API.Deserialize(bs);
  }

  method Serialize(js: JSON) returns (bs: SerializationResult<bytes>) {
    bs := API.Serialize(js);
  }

  method SpecSerialize(js: JSON) returns (bs: SerializationResult<bytes>) {
    bs := Spec.JSON(js);
  }

  method Check(bs: bytes, js: JSON, bs': bytes, sbs': bytes, js': JSON) {
    expect sbs' == bs'; // Serializing changes number representations, escapes, and spacing, so no == bs
    expect js' == js;
  }
}

module MainTests {
  import ZeroCopyWrapper
  import AbstractSyntaxWrapper
  import opened Std.Collections.Seq
  import Std.JSON.Spec
  import opened Std.BoundedInts

  const VECTORS := [
    "true",
    "false",
    "null",
    "\"\"",
    "\"string\"",
    "[\"A\"]",
    "-123.456e-18",
    "[]",
    "[ ]",
    "[1]",
    "[1, 2]",
    "{}",
    "{ \"a\": 1 }",
    "{ \"a\": \"b\" }",
    "{ \"some\" : \"string\", \"and\": [ \"a number\", -123.456e-18 ] }",

    "  true  ",
    " {  } ",
    "\"\\t\\r\\n\\f\"",
    "\"∀ABC // ABC\\u2200\"", // ∀
    "\"🇫🇷 // \\u1f1eb\\u1f1EBABC\"", // 🇫🇷

    "[true, false , null, { \"some\" : \"string\", \"and\": [ \"a number\", -123.456e-18 ] } ]  ",

    /** 
     Stress test - this used to cause stack overflow errors because of non-tail-recursive functions.
     We should have these kinds of tests direclty in the Unicode module too.
     */
    "\"" + Seq.Repeat('a', 100) + "\""
  ]

  @Test
  method Main() {
    ZeroCopyWrapper.TestStrings(VECTORS);
    AbstractSyntaxWrapper.TestStrings(VECTORS);
  }

  @Test
  method SpecTest() {
    expect Spec.EscapeUnicode(7) == ['0' as uint16, '0' as uint16, '0' as uint16, '7' as uint16];
  }
}