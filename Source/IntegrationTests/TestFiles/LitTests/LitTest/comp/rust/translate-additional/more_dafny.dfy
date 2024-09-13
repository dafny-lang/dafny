// RUN: %baredafny translate rs --rust-module-name additional_module "%s"
// RUN: %exits-with -any %rm -f "%S/project_depending_on_dafny/src/additional_module.rs"
// RUN: %mv "%S/more_dafny-rust/src/more_dafny.rs" "%S/project_depending_on_dafny/src/additional_module.rs"
// RUN: "%S/project_depending_on_dafny/cargo" run > "%t"
// RUN: %diff "%s.expect" "%t"

module SubModule {
  function reverse(input: bv16): bv16 {
    ((input & 0xFF) << 8) | ((input & 0xFF00) >> 8)
  }
}

function reverse(input: bv16): (result: bv16) {
  SubModule.reverse(input)
}

lemma reverseDoubleIsIdentity(input: bv16)
  ensures reverse(reverse(input)) == input
{
}