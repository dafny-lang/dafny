
module RandomCSharp replaces DfyRandom {
  import opened CSharpSystem
  import opened Interop
  
  method GetRandomNat ... {
    var random := new Random();
        
    var ceilingInt32opt := IntToInt32(ceiling);
    var ceilingInt32 := ceilingInt32opt.GetOr(Int32.MaxValue);
    Int32.MaxValueValue();
    var zeroOpt := IntToInt32(0);
    var zero := zeroOpt.Extract();
    var resultInt32 := random.Next(zero, ceilingInt32);
    var resultInt := Int32ToInt(resultInt32);
    return resultInt as nat;
  }
}

module Interop {
  import opened CSharpSystem
  import opened Std.Wrappers
  
  method {:axiom} {:extern} IntToInt32(value: int) returns (res: Option<Int32>)
    ensures  
      if value <= Int32.MaxValue.value 
        then res.Some? && res.Extract().value == value
        else res.None?
    
  method {:axiom} {:extern} Int32ToInt(value: Int32) returns (res: int)
    ensures res == value.value
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