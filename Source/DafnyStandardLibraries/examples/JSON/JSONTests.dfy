// TODO: Test for Java and other target languages too

abstract module Wrapper {
  import DafnyStdLibs.JSON.Utils.Str
  import opened DafnyStdLibs.BoundedInts
  import opened DafnyStdLibs.Unicode.UnicodeStringsWithUnicodeChar
  import opened DafnyStdLibs.JSON.Errors

  type JSON
  
  method Deserialize(bs: bytes) returns (js: DeserializationResult<JSON>)
  method SpecSerialize(js: JSON) returns (bs: SerializationResult<bytes>)
  method Serialize(js: JSON) returns (bs: SerializationResult<bytes>)
  method Check(bs: bytes, js: JSON, bs': bytes, sbs': bytes, js': JSON)

  method {:test} TestBytestring(bs: bytes, indent: string) {
    var js  :- expect Deserialize(bs);
    // print indent, "=> ", js, "\n";
    var bs'  :- expect Serialize(js);
    print indent, "=> ", FromUTF8Checked(bs'), "\n";
    var sbs' :- expect SpecSerialize(js);
    print indent, "=> ", FromUTF8Checked(sbs'), "\n";
    var js'  :- expect Deserialize(bs');
    Check(bs, js, bs', sbs', js');
  }

  method {:test} TestString(str: string, indent: string) {
    var bs :- expect ToUTF8Checked(str);
    TestBytestring(bs, indent);
  }

  method {:test} TestStrings(vectors: seq<string>) {
    for i := 0 to |vectors| {
      var input := vectors[i];
      var idx := Str.OfInt(i);
      var indent := seq(|idx| + 1, _ => ' ');
      print "[", idx, "]: ", input, "\n";
      TestString(input, indent);
      print "\n";
    }
  }
}

module JSON.Tests.ZeroCopyWrapper refines Wrapper {
  import opened DafnyStdLibs.Wrappers
  import DafnyStdLibs.JSON.Grammar
  import DafnyStdLibs.JSON.ZeroCopy.API
  import DafnyStdLibs.JSON.ConcreteSyntax.Spec

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

  method {:test} Check(bs: bytes, js: JSON, bs': bytes, sbs': bytes, js': JSON) {
    expect sbs' == bs' == bs;
    expect js' == js; // This doesn't hold in general, since the views could be different
  }
}

module AbstractSyntaxWrapper refines Wrapper {
  import opened DafnyStdLibs.Wrappers
  import DafnyStdLibs.JSON.Grammar
  import DafnyStdLibs.JSON.API
  import DafnyStdLibs.JSON.Values
  import DafnyStdLibs.JSON.Spec

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

  method {:test} Check(bs: bytes, js: JSON, bs': bytes, sbs': bytes, js': JSON) {
    expect sbs' == bs'; // Serializing changes number representations, escapes, and spacing, so no == bs
    expect js' == js;
  }
}

module JSON.Tests {
  import opened DafnyStdLibs.Collections.Seqs

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
    "\"∀ABC // \\u2200ABC\"", // ∀
    "\"🇫🇷 // \\u1f1eb\\u1f1EBABC\"", // 🇫🇷

    "[true, false , null, { \"some\" : \"string\", \"and\": [ \"a number\", -123.456e-18 ] } ]  ",

    // Stress test - this used to cause stack overflow errors because of non-tail-recursive functions.
    // We should have these kinds of tests direclty in the Unicode module too.
    "\"" + Seqs.Repeat('a', 100_000) + "\""
  ]

  method Main() {
    ZeroCopyWrapper.TestStrings(VECTORS);
    AbstractSyntaxWrapper.TestStrings(VECTORS);
  }
}