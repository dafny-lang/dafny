// NONUNIFORM: Rust-specific tests
// RUN: %exits-with 3 %baredafny run --target=rs --enforce-determinism --input "%S/externalclasses.rs" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:extern} ExternalClassContainer {
  method {:extern} Test() returns (i: int)
  trait GetValueHolder {
    function GetValue(): int
    function GetValue2(): int
  }

  class {:extern} ExternalPartialClass extends GetValueHolder {
    constructor {:extern} ()
    function {:extern} GetValue(): int // Error
    function GetValue2(): int {
      1
    }
  }
}

method Main() {
  var c := new ExternalClassContainer.ExternalPartialClass();
}