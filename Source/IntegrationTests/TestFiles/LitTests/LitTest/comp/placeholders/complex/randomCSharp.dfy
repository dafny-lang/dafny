
module RandomCSharp replaces DfyRandom {
  import CSharpSystem
  import CSharpSystemTypes
  import Interop
  
  method GetRandomNat ... {
    // Ignore the ceiling parameter for now
    var random := new CSharpSystem.Random();
    
    var ceilingInt32 := Interop.IntToInt32(ceiling).GetOr(CSharpSystemTypes.Int32.MaxValue);
    assert Interop.Int32ToInt(ceilingInt32) <= ceiling;
    var resultInt32 := random.Next(Interop.IntToInt32(0).Extract(), ceilingInt32);
    var resultInt := Interop.Int32ToInt(resultInt32);
    return resultInt as nat;
  }
}

module Interop {
  import opened CSharpSystemTypes
  import opened DafnyStdLibs.Wrappers
  
  const int32MaxValue := 2147483647
  
  function {:extern} IntToInt32(value: int): Option<Int32>
    ensures match IntToInt32(value) {
      case None        => value > Int32ToInt(Int32.MaxValue)
      case Some(int32) =>  Int32ToInt(int32) == value
    }
    ensures value <= int32MaxValue ==> IntToInt32(value).Some?
    
  function {:extern} Int32ToInt(value: Int32): int
}

module {:extern "System"} CSharpSystemTypes {
  class {:extern "Int32" } Int32 {
    static const {:extern} MaxValue: Int32 
  }
}

module {:extern "System"} CSharpSystem {
  import Interop
  import opened CSharpSystemTypes
  
  class {:extern "Random" } Random {
    constructor {:extern} () { }
    
    method {:extern} Next(minValue: Int32, maxValue: Int32) returns (r: Int32)
      ensures var i := Interop.Int32ToInt(r); Interop.Int32ToInt(minValue) <= i && i < Interop.Int32ToInt(maxValue) 
  }
}