// RUN: %baredafny translate rs --enforce-determinism --rust-module-name additional_module "%S/more_dafny_extern.rs" "%s"
// RUN: %exits-with -any %rm -f "%S/project_depending_on_dafny/src/additional_module.rs"
// RUN: %exits-with -any %rm -f "%S/project_depending_on_dafny/src/more_dafny_extern.rs"
// RUN: %mv "%S/more_dafny-rust/src/more_dafny.rs" "%S/project_depending_on_dafny/src/additional_module.rs"
// RUN: %mv "%S/more_dafny-rust/src/more_dafny_extern.rs" "%S/project_depending_on_dafny/src/more_dafny_extern.rs"
// RUN: "%S/project_depending_on_dafny/cargo" run > "%t"
// RUN: %diff "%s.expect" "%t"

module SubModule {
  function {:axiom} {:extern "extern_dafny", "eight"} Eight(): (r: bv16) ensures r == 8

  function reverse(input: bv16): bv16 {
    ((input & 0xFF) << Eight()) | ((input & 0xFF00) >> Eight())
  }
}

function reverse(input: bv16): (result: bv16) {
  SubModule.reverse(input)
}

lemma reverseDoubleIsIdentity(input: bv16)
  ensures reverse(reverse(input)) == input
{
}
