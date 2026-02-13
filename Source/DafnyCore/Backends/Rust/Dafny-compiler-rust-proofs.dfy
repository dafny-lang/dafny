include "../Dafny/AST.dfy"

/*These modules do not contain any compiled code because they
  only proves properties about DCOMP. In a sense, it's a test file. */
@Compile(false)
module {:extern "RASTProofs"} RASTProofs {
  import opened RAST
  lemma AboutGatherSimpleQuotes(docstring: string, acc: string)
    ensures
      var r := GatherSimpleQuotes(docstring, acc);
      && |acc| <= |r|
      && |r[|acc|..]| <= |docstring|
      && r == acc + docstring[..|r[|acc|..]|]
      && (forall i | |acc| <= i < |r| :: r[i] == '`')
      && (|docstring| > |r[|acc|..]| ==>
            docstring[|r[|acc|..]|] != '`')
  {
    var r := GatherSimpleQuotes(docstring, acc);
    if |docstring| == 0 || docstring[0] != '`' {

    } else {

    }
  }
}
@Compile(false)
module {:extern "DafnyToRustCompilerProofs"} DafnyToRustCompilerProofs {
  import opened DafnyToRustCompiler
  import opened DafnyToRustCompilerDefinitions

  ghost predicate IsDafnyId(s: string) {
    && |s| > 0 && s[0] in "aqkhd" &&
       IsDafnyIdTail(s[1..])
  }

  ghost predicate IsDafnyIdTail(s: string) {
    |s| == 0 ||
    (s[0] in "aqkhd_?'#." && IsDafnyIdTail(s[1..]))
  }

  lemma IsDafnyIdImpliesDafnyIdTail(s: string)
    requires IsDafnyId(s)
    ensures IsDafnyIdTail(s)
  {}

  function DafnyEscape(s: string): string {
    if |s| == 0 then "" else
    if s[0] == '_' then "__" + DafnyEscape(s[1..]) else
    if s[0] == '?' then "_q" + DafnyEscape(s[1..]) else
    if s[0] == '\'' then "_k" + DafnyEscape(s[1..]) else
    if s[0] == '#' then "_h" + DafnyEscape(s[1..]) else
    [s[0]] + DafnyEscape(s[1..])
  }

  function DafnyUnescape(s: string): string {
    if |s| <= 1 then s else
    if s[0] == '_' then
      if s[1] == '_' then "_" + DafnyUnescape(s[2..]) else
      if s[1] == 'q' then "?" + DafnyUnescape(s[2..]) else
      if s[1] == 'k' then "'" + DafnyUnescape(s[2..]) else
      if s[1] == 'h' then "#" + DafnyUnescape(s[2..]) else
      s[..1] + DafnyUnescape(s[1..])
    else
      s[..1] + DafnyUnescape(s[1..])
  }

  lemma DafnyEscapeBijective(s: string)
    ensures DafnyUnescape(DafnyEscape(s)) == s
  {
    if |s| == 0 {
    } else {
      DafnyEscapeBijective(s[1..]);
      if s[0] == '_' {
      } else if s[0] == '?' {
      } else if s[0] == '\'' {
      } else if s[0] == '#' {
      } else {
      }
    }
  }

  lemma DafnyEscapeCharacteristic(s: string)
    requires IsDafnyIdTail(s)
    ensures IsDafnyEncodedIdTail(DafnyEscape(s))
  {
    if |s| == 0 {
    } else {
      DafnyEscapeCharacteristic(s[1..]);
      if s[0] == '_' {
      } else if s[0] == '?' {
      } else if s[0] == '\'' {
      } else if s[0] == '#' {
      } else {
      }
    }
  }

  function ReverseReplaceDots(i: string): string {
    if |i| <= 1 then i
    else if i[0] == '_' then
      if i[1] == 'd' then "." + ReverseReplaceDots(i[2..])
      else [i[0]] + [i[1]] + ReverseReplaceDots(i[2..])
    else
      [i[0]] + ReverseReplaceDots(i[1..])
  }

  predicate IsDafnyEncodedIdTail(i: string) {
    if |i| == 0 then true
    else
    if i[0] == '_' then
      |i| >= 2 &&
      i[1] in ESCAPING && IsDafnyEncodedIdTail(i[2..])
    else
      (i[0] in SAMPLE_LETTERS || i[0] == '.') &&
      IsDafnyEncodedIdTail(i[1..])
  }

  // Subset of characters supported in Dafny identifiers, for proof purposes
  const SAMPLE_LETTERS := "aqkhd"

  // Letters that can come after a "_" in Dafny identifiers
  // __ => _
  // _q => ?
  // _k => '
  // _h => #
  const ESCAPING := "_qkh"

  ghost predicate IsDafnyEncodedId(i: string) {
    if |i| == 0 then false
    else i[0] in SAMPLE_LETTERS && IsDafnyEncodedIdTail(i[1..])
  }

  lemma DafnyEscapeCorrect(s: string)
    requires IsDafnyIdTail(s)
    ensures IsDafnyEncodedIdTail(DafnyEscape(s))
            && (IsDafnyId(s) && |s| > 0 ==> DafnyEscape(s)[0] in "aqkhd")
  {
    if |s| == 0 {
    } else {
      if s[0] == '_' { // "__" + DafnyEscape(s[1..])
      } else if s[0] == '?' { // "_q" + DafnyEscape(s[1..]) else
      } else if s[0] == '\'' { // "_k" + DafnyEscape(s[1..]) else
      } else if s[0] == '#' { // "_h" + DafnyEscape(s[1..]) else=
      } else { // [s[0]] + DafnyEscape(s[1..])=
        DafnyEscapeCorrect(s[1..]);
      }
    }
  }
  // replaceDots is not invertible generally speaking.
  // Indeed, both _d and . get translated to _d.
  lemma ReplaceDotsNotInvertible()
    ensures replaceDots("_d") == replaceDots(".")
    ensures !IsDafnyEncodedIdTail("_d")
  {}

  // However, if we restrict ourself to a Dafny encoding, it's invertible
  @ResourceLimit("2500e3")
  @IsolateAssertions
  lemma ReplaceDotsInvertible(i: string)
    requires IsDafnyEncodedIdTail(i)
    ensures ReverseReplaceDots(replaceDots(i)) == i
  {
    if |i| == 0 {
    } else if i[0] == '.' { //"_d" + replaceDots(i[1..])
      ReplaceDotsInvertible(i[1..]);
      assert ReverseReplaceDots(replaceDots(i)) == i;
    } else { // [i[0]] + replaceDots(i[1..])
      assert replaceDots(i) == [i[0]] + replaceDots(i[1..]);
      if i[0] == '_' {
        assert |i| >= 2 &&
               i[1] in "_qkh" && IsDafnyEncodedIdTail(i[2..]);
        assert [i[0]] + replaceDots(i[1..]) == [i[0]] + [i[1]] + replaceDots(i[2..]);
        ReplaceDotsInvertible(i[2..]);
        assert ReverseReplaceDots(replaceDots(i)) == i;
      } else {
        ReplaceDotsInvertible(i[1..]);
        assert ReverseReplaceDots(replaceDots(i)) == i;
      }
    }
  }

  // The reason why escapeIdent is correct is that
  // - It receives either
  //     - a Dafny-encoded Id that has no special character (only letters + "__" which came from "_")
  //       and is not a reserved Rust keyword
  //       ==> Use idiomatic rust
  //     - a is_tuple_numeric like _<1 or 2 digits>
  //       ==> Use idiomatic rust
  //     - a is_tuple_builder like ___hMake<1 or 2 digits>
  //     - a dafny-generated identifier that starts with a "_" like "_module"
  //     - A rust keyword
  //       ==> use "r#" + rust keyword
  //     - Anything else
  //       ==> use "r#_" + replaceDot
  // - The reverse function is such that
  //   - If the input is a Dafny-encoded Id or a tuple numeric,
  //     it can find the original identifier based in the output

  lemma BetterTupleBuilderNameNotRsharp(i: string)
    ensures is_tuple_builder(i) ==>
              var s := better_tuple_builder_name(i);
              s[0..2] != "r#"
  {}

  lemma IdiomaticRustNotRsharp(i: string)
    ensures
      !has_special(i)
      ==>
        |idiomatic_rust(i)| < 1 || idiomatic_rust(i)[0] != '#'
  {
    if !has_special(i) {
      var s := idiomatic_rust(i);
      if |i| == 0 {
      } else if i[0] == '_' {
        var s := "_" + idiomatic_rust(i[2..]);
        assert s[0] == '_';
      } else {
        var s := [i[0]] + idiomatic_rust(i[1..]);
        assert s[0] == i[0];
      }
    }
  }

  @Fuel(2, 3, "has_special")
  lemma EscapeIdentExamples()
    ensures escapeIdent("i") == "i"   // Loop variable
    ensures escapeIdent("_1") == "_1" // tuple deconstructor
    ensures escapeIdent("_m") == "_m" // any hidden variable
    ensures escapeIdent("___hMake1") == "_T1" // tuple deconstructor
    ensures escapeIdent("h__w") == "h_w" // only letters and underscore
    ensures escapeIdent("h_kw") == "_h_kw" //contains special char
    ensures escapeIdent("fn") == "r#fn" // Keyword
  {
    assert has_special("h_kw");
  }

  // Just convert all underscores to double underscores
  function ReverseIdiomaticRust(s: string): string {
    if |s| == 0 then ""
    else if s[0] == '_' then
      "__" + ReverseIdiomaticRust(s[1..])
    else
      [s[0]] + ReverseIdiomaticRust(s[1..])
  }

  lemma {:rlimit 200} IdiomaticRustInvertible(i: string)
    requires !has_special(i)
    ensures ReverseIdiomaticRust(idiomatic_rust(i)) == i
  {
    if |i| == 0 {
    } else if i[0] == '_' {
      IdiomaticRustInvertible(i[2..]);
      assert 2 <= |i| && i[1] == '_';
      var ss := ['_'] + idiomatic_rust(i[2..]);
      assert ss[0] == '_' && |ss| != 0;
    } else {
      IdiomaticRustInvertible(i[1..]);
    }
  }

  function UnescapeIdent(s: string): string {
    if |s| >= 1 && s[0] == '_' then
      if is_tuple_numeric(s) then
        s
      else if |s| >= 2 && s[1] == 'T' then
        "___hMake" + s[2..] // Tuple builder
      else if s == "_self" || s == "_Self" then
        s[1..]
      else
        ReverseReplaceDots(s[1..]) // We remove the extra "_" prefix and place dots again
    else if |s| >= 2 && s[0..2] == "r#" then
      s[2..] // Reserved identifier
    else // Idiomatic rust
      ReverseIdiomaticRust(s)
  }

  lemma TupleIdentInvertible(i: string)
    requires is_tuple_numeric(i)
    ensures UnescapeIdent(escapeIdent(i)) == i
  {
  }

  lemma {:rlimit 500} TupleBuilderInvertible(i: string)
    requires !is_tuple_numeric(i)
    requires is_tuple_builder(i)
    ensures UnescapeIdent(escapeIdent(i)) == i
  {
    var s := "_T" + i[8..];
    calc {
      UnescapeIdent(escapeIdent(i));
      UnescapeIdent(s);
      i[0..8] + s[2..];
      i;
    }
  }

  lemma {:rlimit 800} ReservedRustInvertible(i: string)
    requires !is_tuple_numeric(i)
    requires !is_tuple_builder(i)
    requires i in reserved_rust
    ensures UnescapeIdent(escapeIdent(i)) == i
  {
    assert i[0] != '_';
    var s := "r#" + i;
    calc {
      UnescapeIdent(escapeIdent(i));
      UnescapeIdent(s);
      s[2..];
      i;
    }
  }

  lemma {:rlimit 800} EscapeIdentInvertibleForIdiomaticRust(i: string)
    requires IsDafnyEncodedId(i) // Needed to ensure i does not start with '_'
    requires !is_tuple_numeric(i)
    requires !is_tuple_builder(i)
    requires i !in reserved_rust
    requires is_idiomatic_rust_id(i)
    ensures UnescapeIdent(escapeIdent(i)) == i
  {
    var s := idiomatic_rust(i);
    IdiomaticRustNotRsharp(i);
    assert |s| < 2 || s[0..2] != "r#" by {
      if |s| >= 2 && s[0..2] == "r#" {
        assert s[1] == '#';
        IdiomaticRustNotRsharp(i[1..]);
      }
    }
    assert s[0] != '_';
    calc {
      UnescapeIdent(escapeIdent(i));
      UnescapeIdent(idiomatic_rust(i));
      ReverseIdiomaticRust(idiomatic_rust(i));
      { IdiomaticRustInvertible(i); }
      i;
    }
  }

  lemma {:rlimit 800} EscapeIdentInvertibleForDafnyGeneratedId(i: string)
    requires IsDafnyEncodedId(i)
    requires !is_tuple_numeric(i)
    requires !is_tuple_builder(i)
    requires i !in reserved_rust
    requires !is_idiomatic_rust_id(i)
    requires is_dafny_generated_id(i)
    ensures UnescapeIdent(escapeIdent(i)) == i
  {
    assert escapeIdent(i) == i;
    var s := i;
    assert |s| >= 1 && s[0] == '_';
    assert !(|s| >= 2 && s[1] == 'T');
    assert !(s == "_self" || s == "_Self");
    calc {
      UnescapeIdent(s);
      s;
    }
  }

  lemma {:rlimit 800} EverythingElseInvertible(i: string)
    requires IsDafnyEncodedId(i) // Needed to ensure i does not start with '_'
    requires !is_tuple_numeric(i)
    requires !is_tuple_builder(i)
    requires i !in reserved_rust
    requires !is_idiomatic_rust_id(i)
    requires !is_dafny_generated_id(i)
    ensures UnescapeIdent(escapeIdent(i)) == i
  {
    var r := replaceDots(i);
    var s := "_" + r;
    assert escapeIdent(i) == s;
    assert |s| >= 1 && s[0] == '_';
    assert !(|s| >= 2 && s[1] == 'T');
    assert !(s == "_self" || s == "_Self");
    assert |i| > 0;
    if i[0] == '_' {
      assert i[0] == '_'; // So if i[0] is not '_'
      assert UnescapeIdent(escapeIdent(i)) == i;
    } else {
      calc {
        UnescapeIdent(s);
        ReverseReplaceDots(s[1..]);
        ReverseReplaceDots(r);
        ReverseReplaceDots(replaceDots(i));
        { ReplaceDotsInvertible(i); }
        i;
      }
    }
  }

  // That's the lemma that shows
  lemma EscapeIdentInvertible(i: string)
    requires is_tuple_numeric(i) // _0 _1 ...                 => _0, _1 ...
             || is_tuple_builder(i) // ___hMake0, ____hMake1 ... => _T0, _T1 ...
             || i in reserved_rust  // fn, impl, mod ...         => r#fn, r#impl, r#mod...
             || IsDafnyEncodedId(i) // i                         => i
    // create_struct             => create_struct
    //  c#ons.tant?'              => r#_c_hons_dtant_q_k
    ensures UnescapeIdent(escapeIdent(i)) == i
  {
    if is_tuple_numeric(i) {
      TupleIdentInvertible(i);
    } else if is_tuple_builder(i) {
      TupleBuilderInvertible(i);
    } else if i in reserved_rust {
      assert UnescapeIdent(escapeIdent(i)) == i;
    } else if is_idiomatic_rust_id(i) {
      EscapeIdentInvertibleForIdiomaticRust(i);
    } else if is_dafny_generated_id(i) { // TODO: Mov up so that we can put it in specifications
      EscapeIdentInvertibleForDafnyGeneratedId(i);
    } else {
      EverythingElseInvertible(i);
    }
  }

}
