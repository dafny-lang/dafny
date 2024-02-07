




include "../Dafny/AST.dfy"

module {:extern "DCOMPProofs"} {:compile false} DCOMPProofs refines DCOMP {

  ghost predicate IsDafnyIdTail(s: string) {
    |s| == 0 ||
    (s[0] in "aqkhd_?'#." && IsDafnyIdTail(s[1..]))
  }

  ghost predicate IsDafnyId(s: string) {
    && |s| > 0 && s[0] in "aqkhd" &&
       IsDafnyIdTail(s[1..])
  }
  lemma IsDafnyIdImpliesDafnyIdTail(s: string)
    requires IsDafnyId(s)
    ensures IsDafnyIdTail(s)
  {}

  function dafnyEscape(s: string): string {
    if |s| == 0 then "" else
    if s[0] == '_' then "__" + dafnyEscape(s[1..]) else
    if s[0] == '?' then "_q" + dafnyEscape(s[1..]) else
    if s[0] == '\'' then "_k" + dafnyEscape(s[1..]) else
    if s[0] == '#' then "_h" + dafnyEscape(s[1..]) else
    [s[0]] + dafnyEscape(s[1..])
  }

  function dafnyEscapeReverse(s: string): string {
    if |s| <= 1 then s else
    if s[0] == '_' then
      if s[1] == '_' then "_" + dafnyEscapeReverse(s[2..]) else
      if s[1] == 'q' then "?" + dafnyEscapeReverse(s[2..]) else
      if s[1] == 'k' then "'" + dafnyEscapeReverse(s[2..]) else
      if s[1] == 'h' then "#" + dafnyEscapeReverse(s[2..]) else
      s[..1] + dafnyEscapeReverse(s[1..])
    else
      s[..1] + dafnyEscapeReverse(s[1..])
  }

  lemma dafnyEscapeBijective(s: string)
    ensures dafnyEscapeReverse(dafnyEscape(s)) == s
  {
    if |s| == 0 {
    } else {
      dafnyEscapeBijective(s[1..]);
      if s[0] == '_' {
      } else if s[0] == '?' {
      } else if s[0] == '\'' {
      } else if s[0] == '#' {
      } else {
      }
    }
  }

  lemma dafnyEscapeCharacteristic(s: string)
    requires IsDafnyIdTail(s)
    ensures isDafnyEncodedIdTail(dafnyEscape(s))
  {
    if |s| == 0 {
    } else {
      dafnyEscapeCharacteristic(s[1..]);
      if s[0] == '_' {
      } else if s[0] == '?' {
      } else if s[0] == '\'' {
      } else if s[0] == '#' {
      } else {
      }
    }
  }

  function reverseReplaceDots(i: string): string {
    if |i| <= 1 then i
    else if i[0] == '_' then
      if i[1] == 'd' then "." + reverseReplaceDots(i[2..])
      else [i[0]] + [i[1]] + reverseReplaceDots(i[2..])
    else
      [i[0]] + reverseReplaceDots(i[1..])
  }

  predicate isDafnyEncodedIdTail(i: string) {
    if |i| == 0 then true
    else
    if i[0] == '_' then
      |i| >= 2 &&
      i[1] in "_qkh" && isDafnyEncodedIdTail(i[2..])
    else
      i[0] in "aqkhd." &&
      isDafnyEncodedIdTail(i[1..])
  }

  predicate isDafnyEncodedId(i: string) {
    if |i| == 0 then true
    else i[0] in "aqkhd" && isDafnyEncodedIdTail(i[1..])
  }

  lemma dafnyEscapeCorrect(s: string)
    requires IsDafnyIdTail(s)
    ensures isDafnyEncodedIdTail(dafnyEscape(s))
            && (IsDafnyId(s) && |s| > 0 ==> dafnyEscape(s)[0] in "aqkhd")
  {
    if |s| == 0 {
    } else {
      if s[0] == '_' { // "__" + dafnyEscape(s[1..])
      } else if s[0] == '?' { // "_q" + dafnyEscape(s[1..]) else
      } else if s[0] == '\'' { // "_k" + dafnyEscape(s[1..]) else
      } else if s[0] == '#' { // "_h" + dafnyEscape(s[1..]) else=
      } else { // [s[0]] + dafnyEscape(s[1..])=
        dafnyEscapeCorrect(s[1..]);
      }
    }
  }
  // replaceDots is not reversible generally speaking.
  // Indeed, both _d and . get translated to _d.
  lemma replaceDotsNotReversible()
    ensures replaceDots("_d") == replaceDots(".")
    ensures !isDafnyEncodedIdTail("_d")
  {}

  // However, if we restrict ourself to a Dafny encoding, it's reversible
  lemma {:rlimit 500}
  replaceDotsReversible(i: string)
    requires isDafnyEncodedIdTail(i)
    ensures reverseReplaceDots(replaceDots(i)) == i
  {
    if |i| == 0 {
    } else if i[0] == '.' { //"_d" + replaceDots(i[1..])
      replaceDotsReversible(i[1..]);
      assert reverseReplaceDots(replaceDots(i)) == i;
    } else { // [i[0]] + replaceDots(i[1..])
      assert replaceDots(i) == [i[0]] + replaceDots(i[1..]);
      if i[0] == '_' {
        assert |i| >= 2 &&
               i[1] in "_qkh" && isDafnyEncodedIdTail(i[2..]);
        replaceDotsReversible(i[2..]);
        assert reverseReplaceDots(replaceDots(i)) == i;
      } else {
        replaceDotsReversible(i[1..]);
        assert reverseReplaceDots(replaceDots(i)) == i;
      }
    }
  }

  // The reason why escapeIndent is correct is that
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

  lemma better_tuple_builder_name_not_rsharp(i: string)
    ensures is_tuple_builder(i) ==>
              var s := better_tuple_builder_name(i);
              s[0..2] != "r#"
  {}

  lemma idiomatic_rust_not_rsharp(i: string)
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

  lemma {:fuel has_special, 2, 3} escapeIndentExamples()
    ensures escapeIdent("i") == "i"   // Loop variable
    ensures escapeIdent("_1") == "_1" // tuple deconstructor
    ensures escapeIdent("_m") == "_m" // any hidden variable
    ensures escapeIdent("___hMake1") == "_T1" // tuple deconstructor
    ensures escapeIdent("h__w") == "h_w" // only letters and underscore
    ensures escapeIdent("h_kw") == "r#_h_kw" //contains special char
    ensures escapeIdent("fn") == "r#fn" // Keyword
  {
    assert has_special("h_kw");
  }

  // Just convert all underscores to double underscores
  function reverse_idiomatic_rust(s: string): string {
    if |s| == 0 then ""
    else if s[0] == '_' then
      "__" + reverse_idiomatic_rust(s[1..])
    else
      [s[0]] + reverse_idiomatic_rust(s[1..])
  }

  lemma {:rlimit 200} idiomatic_rust_reversible(i: string)
    requires !has_special(i)
    ensures reverse_idiomatic_rust(idiomatic_rust(i)) == i
  {
    if |i| == 0 {
    } else if i[0] == '_' {
      idiomatic_rust_reversible(i[2..]);
      assert 2 <= |i| && i[1] == '_';
      var ss := ['_'] + idiomatic_rust(i[2..]);
      assert ss[0] == '_' && |ss| != 0;
    } else {
      idiomatic_rust_reversible(i[1..]);
    }
  }

  function reverseEscapeIdent(s: string): string {
    if |s| >= 2 && s[0..2] == "r#" then
      if |s| >= 3 && s[2] == '_' then
        reverseReplaceDots(s[3..]) // General escape
      else
        s[2..] // Keyword
    else if |s| >= 1 && s[0] == '_' then
      if |s| >= 2 && s[1] == 'T' then
        "___hMake" + s[2..] // Tuple builder
      else if is_tuple_numeric(s) then
        s
      else
        s
    else // Idiomatic rust
      reverse_idiomatic_rust(s)
  }

  lemma tupleIdentReversible(s: string)
    requires is_tuple_numeric(s)
    ensures reverseEscapeIdent(escapeIdent(s)) == s
  {}

  lemma {:rlimit 500} tupleBuilderReversible(i: string)
    requires !is_tuple_numeric(i)
    requires is_tuple_builder(i)
    ensures reverseEscapeIdent(escapeIdent(i)) == i
  {
    var s := "_T" + i[8..];
    calc {
      reverseEscapeIdent(escapeIdent(i));
      reverseEscapeIdent(s);
      i[0..8] + s[2..];
      i;
    }
  }

  lemma {:rlimit 800} reservedRustReversible(i: string)
    requires !is_tuple_numeric(i)
    requires !is_tuple_builder(i)
    requires i in reserved_rust
    ensures reverseEscapeIdent(escapeIdent(i)) == i
  {
    assert i[0] != '_';
    var s := "r#" + i;
    calc {
      reverseEscapeIdent(escapeIdent(i));
      reverseEscapeIdent(s);
      s[2..];
      i;
    }
  }

  lemma {:rlimit 800} idiomaticRustReversible(i: string)
    requires isDafnyEncodedId(i) // Needed to ensure i does not start with '_'
    requires !is_tuple_numeric(i)
    requires !is_tuple_builder(i)
    requires i !in reserved_rust
    requires is_idiomatic_rust(i)
    ensures reverseEscapeIdent(escapeIdent(i)) == i
  {
    var s := idiomatic_rust(i);
    idiomatic_rust_not_rsharp(i);
    assert |s| < 2 || s[0..2] != "r#" by {
      if |s| >= 2 && s[0..2] == "r#" {
        assert s[1] == '#';
        idiomatic_rust_not_rsharp(i[1..]);
      }
    }
    assert s[0] != '_';
    calc {
      reverseEscapeIdent(escapeIdent(i));
      reverseEscapeIdent(idiomatic_rust(i));
      reverse_idiomatic_rust(idiomatic_rust(i));
      { idiomatic_rust_reversible(i); }
      i;
    }
  }

  lemma {:rlimit 800} dafnyGeneratedIdReversible(s: string)
    requires !is_tuple_numeric(s)
    requires !is_tuple_builder(s)
    requires s !in reserved_rust
    requires !is_idiomatic_rust(s)
    requires is_dafny_generated_id(s)
    ensures reverseEscapeIdent(escapeIdent(s)) == s
  {
  }

  lemma {:rlimit 800} everythingElseReversible(i: string)
    requires isDafnyEncodedId(i) // Needed to ensure i does not start with '_'
    requires !is_tuple_numeric(i)
    requires !is_tuple_builder(i)
    requires i !in reserved_rust
    requires !is_idiomatic_rust(i)
    requires !is_dafny_generated_id(i)
    ensures reverseEscapeIdent(escapeIdent(i)) == i
  {
    var r := replaceDots(i);
    var s := "r#_" + r;
    assert |s| >= 2 && s[0..2] == "r#";
    assert |s| >= 3 && s[2] == '_';
    assert s[3..] == r;
    calc {
      reverseEscapeIdent(escapeIdent(i));
      reverseEscapeIdent(s);
      reverseReplaceDots(replaceDots(i));
      { replaceDotsReversible(i); }
      i;
    }
  }

  // That's the lemma that shows
  lemma escapeIdentReversible(i: string)
    requires is_tuple_numeric(i) // _0 _1 ...                 => _0, _1 ...
             || is_tuple_builder(i) // ___hMake0, ____hMake1 ... => _T0, _T1 ...
             || i in reserved_rust  // fn, impl, mod ...         => r#fn, r#impl, r#mod...
             || isDafnyEncodedId(i) // i                         => i
                                    // create_struct             => create_struct
    //  c#ons.tant?'              => r#_c_hons_dtant_q_k
    ensures reverseEscapeIdent(escapeIdent(i)) == i
  {
    if is_tuple_numeric(i) {
      tupleIdentReversible(i);
    } else if is_tuple_builder(i) {
      tupleBuilderReversible(i);
    } else if i in reserved_rust {
      assert reverseEscapeIdent(escapeIdent(i)) == i;
    } else if is_idiomatic_rust(i) {
      idiomaticRustReversible(i);
    } else if is_dafny_generated_id(i) { // TODO: Mov up so that we can put it in specifications
      dafnyGeneratedIdReversible(i);
    } else {
      everythingElseReversible(i);
    }
  }

}
