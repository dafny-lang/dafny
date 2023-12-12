
module RandomGo replaces DfyRandom {
  import opened Interop
  // import opened Math
  // import Math.Random
  import opened Types

  method GetRandomNat ... {
    
    var ceilingInt32: Int32 := IntToInt32(ceiling).GetOr(Interop.MaxInt32);
    Interop.MaxInt32Value();
    var resultInt32 := Interop.Int31(ceilingInt32);
    var resultInt := Int32ToInt(resultInt32);
    return resultInt as nat;
  }
}

module Interop {
  import opened Std.Wrappers
  import opened Types

  function {:extern} IntToInt32(value: int): Option<Int32>
    ensures var r := IntToInt32(value); 
      if value <= MaxInt32.value 
        then r.Some? && r.Extract().value == value
        else r.None?
    
  function {:extern} Int32ToInt(value: Int32): int
    ensures Int32ToInt(value) == value.value

  // Even a const access becomes a function call in the Go translation, so this had to be in Interop
  const {:extern "MaxInt32"} MaxInt32: Int32
  lemma {:axiom} MaxInt32Value() ensures MaxInt32.value == 2147483647

  // We can't seem to refer to something from a nested module, so this has to be in Interop
  method {:extern "Int31n"} Int31(maxValue: Int32) returns (r: Int32)
    ensures 0 <= r.value && r.value < maxValue.value
}

/*
module {:extern "math"} {:dummyImportMember "MaxInt32", false} Math {
  import opened Types

  // We can't seem to refer to something from a nested module, so this has to be in Interop
  module {:extern "math/rand" } Random {
    import opened Types
    method {:extern "Int31n"} Int31(maxValue: Int32) returns (r: Int32)
      ensures 0 <= r.value && r.value < maxValue.value
  }
}
*/

module {:extern "Types"} {:dummyImportMember "Dummy__", true} Types {
  class {:extern "", "int32" } Int32 {
    ghost var value: int
  }
}
 