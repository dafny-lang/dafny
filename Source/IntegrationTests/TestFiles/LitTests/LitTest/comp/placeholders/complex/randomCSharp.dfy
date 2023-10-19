
module RandomCSharp replaces DfyRandom {
  import opened CSharpSystem
  import opened Interop
  
  method GetRandomNat ... {
    var random := new Random();
    
    var ceilingInt32 := IntToInt32(ceiling).GetOr(Int32.MaxValue);
    var resultInt32 := random.Next(IntToInt32(0).Extract(), ceilingInt32);
    var resultInt := Int32ToInt(resultInt32);
    return resultInt as nat;
  }
}

module Interop {
  import opened CSharpSystem
  import opened DafnyStdLibs.Wrappers
  
  const int32MaxValue := 2147483647
  
  function {:extern} IntToInt32(value: int): Option<Int32>
    ensures match IntToInt32(value) {
      case None        => value > Int32ToInt(Int32.MaxValue)
      case Some(int32) => int32.value == value
    }
    ensures value <= int32MaxValue ==> IntToInt32(value).Some?
    
  function {:extern} Int32ToInt(value: Int32): int
    ensures Int32ToInt(value) == value.value
}

module {:extern "System"} CSharpSystem {
  
  class {:extern "Int32" } Int32 {
    ghost var value: int
    // Would be nice to have an ensures here that equates it to 2147483647
    // So we would not need Interop.int32MaxValue
    static const {:extern} MaxValue: Int32
  }
  
  class {:extern "Random" } Random {
    constructor {:extern} () { }
    
    method {:extern} Next(minValue: Int32, maxValue: Int32) returns (r: Int32)
      ensures minValue.value <= r.value && r.value < maxValue.value
  }
}