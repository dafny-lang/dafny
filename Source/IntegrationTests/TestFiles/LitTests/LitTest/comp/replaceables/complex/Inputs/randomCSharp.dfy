
module RandomCSharp replaces DfyRandom {
  import opened CSharpSystem
  import opened Interop
  
  method GetRandomNat ... {
    var random := new Random();
    
    var ceilingInt32 := IntToInt32(ceiling).GetOr(Int32.MaxValue);
    Int32.MaxValueValue();
    var resultInt32 := random.Next(IntToInt32(0).Extract(), ceilingInt32);
    var resultInt := Int32ToInt(resultInt32);
    return resultInt as nat;
  }
}

module Interop {
  import opened CSharpSystem
  import opened Std.Wrappers
  
  function {:axiom} {:extern} IntToInt32(value: int): Option<Int32>
    ensures var r := IntToInt32(value); 
      if value <= Int32.MaxValue.value 
        then r.Some? && r.Extract().value == value
        else r.None?
    
  function {:axiom} {:extern} Int32ToInt(value: Int32): int
    ensures Int32ToInt(value) == value.value
}

module {:extern "System"} CSharpSystem {
  
  class {:extern "Int32" } Int32 {
    ghost var value: int
    static const {:extern} MaxValue: Int32
    
    static lemma {:axiom} MaxValueValue() ensures MaxValue.value == 2147483647
  }
  
  class {:extern "Random" } Random {
    constructor {:extern} ()
    
    method {:axiom} {:extern} Next(minValue: Int32, maxValue: Int32) returns (r: Int32)
      ensures minValue.value <= r.value && r.value < maxValue.value
  }
}