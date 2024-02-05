// This test asserts the current behavior for trying to use
// standard libraries in contexts that aren't supported:
// not providing the option, providing incompatible options,
// commands like formatting, etc.

// Valid:

// RUN: %verify --standard-libraries:true "%s" > "%t"
// RUN: %verify --standard-libraries:true --track-print-effects "%s" >> "%t"

// Invalid:

// RUN: %exits-with 2 %verify "%s" >> "%t"
// RUN: %exits-with 1 %verify --standard-libraries:true --unicode-char:false "%s" >> "%t"
// RUN: %exits-with 1 %baredafny format --standard-libraries "%s" 2>> "%t"
// RUN: %diff "%s.expect" "%t"

module UsesWrappers {

  import opened Std.Wrappers

  function SafeDiv(a: int, b: int): Option<int> {
    if b == 0 then None else Some(a/b)
  }
}
