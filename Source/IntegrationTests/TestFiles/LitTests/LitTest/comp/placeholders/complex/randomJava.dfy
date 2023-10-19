
module RandomJava replaces DfyRandom {
  import opened Interop
  import opened JavaTypes
  import opened JavaRest
  
  method GetRandomNat ... {
    // Ignore the ceiling parameter for now
    var random := new JavaRandom();
    
    var ceilingInt32 := IntToInt32(ceiling).GetOr(JavaInteger.MaxValue);
    assert Int32ToInt(ceilingInt32) <= ceiling;
    var resultInt32 := random.Next(ceilingInt32);
    var resultInt := Int32ToInt(resultInt32);
    return resultInt as nat;
  }
}

module Interop {
  import opened JavaTypes
  import opened DafnyStdLibs.Wrappers
  
  const int32MaxValue := 2147483647
  
  function {:extern} IntToInt32(value: int): Option<Int32>
    ensures match IntToInt32(value) {
      case None        => value > Int32ToInt(JavaInteger.MaxValue)
      case Some(int32) =>  Int32ToInt(int32) == value
    }
    ensures value <= int32MaxValue ==> IntToInt32(value).Some?
    
  function {:extern} Int32ToInt(value: Int32): int
}
  
module {:extern ""} JavaTypes {
  class {:extern "int" } Int32 {
  }

  class {:extern "java.lang.Integer" } JavaInteger {
    // Would be nice to have an ensures here that equates it to 2147483647
    // So we would not need Interop.int32MaxValue
    static const {:extern "MAX_VALUE"} MaxValue: Int32 
  }

}
module {:extern "java.util"} JavaRest {
  import opened JavaTypes
  import opened Interop
  
  class {:extern "Random" } JavaRandom {
    constructor {:extern} () { }
    
    method {:extern "nextInt"} Next(bound: Int32) returns (r: Int32)
      ensures var i := Int32ToInt(r); 0 <= i && i < Int32ToInt(bound) 
  }
}