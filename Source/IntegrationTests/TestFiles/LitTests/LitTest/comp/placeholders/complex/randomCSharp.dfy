
module RandomCSharp replaces DfyRandom {
  import CSharpSystem
  import Interop
  
  method GetRandomNat ... {
    // Ignore the ceiling parameter for now
    var random := new CSharpSystem.Random();
    var resultInt32 := random.Next();
    var resultInt := Interop.Int32ToInt(resultInt32);
    return resultInt as nat;
  }
}

module Interop {
  import CSharpSystemTypes
  
  function {:extern} Int32ToInt(value: CSharpSystemTypes.Int32): int
}

module {:extern "System"} CSharpSystemTypes {
  class {:extern "Int32" } Int32 { }
}

module {:extern "System"} CSharpSystem {
  import Interop
  import opened CSharpSystemTypes
  
  class {:extern "Random" } Random {
    constructor {:extern} () { }
    
    method {:extern} Next() returns (r: Int32)
      ensures Interop.Int32ToInt(r) >= 0
  }
}