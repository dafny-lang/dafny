
module RandomJava replaces DfyRandom {
  import opened Interop
  import opened JavaLang
  import opened JavaRest
  
  method GetRandomNat ... {
    var random := new JavaRandom();
    
    var ceilingInt32opt := IntToInt32(ceiling);
    var baseIntMaxValue := IntegerMaxValue();
    var ceilingInt32 := ceilingInt32opt.GetOr(baseIntMaxValue);
    assert ceilingInt32.value <= ceiling;
    var resultInt32 := random.Next(ceilingInt32);
    var resultInt := Int32ToInt(resultInt32);
    return resultInt as nat;
  }
}

module Interop {
  import opened JavaLang
  import opened Std.Wrappers
  
  const int32MaxValue := 2147483647
  
  method {:axiom} {:extern} IntToInt32(value: int) returns (res: Option<Integer>)
    ensures
      if value <= int32MaxValue 
        then res.Some? && res.Extract().value == value
        else res.None?
    
  method {:axiom} {:extern} Int32ToInt(value: Integer) returns (res: int)
    ensures res == value.value
  
  method {:axiom} {:extern} IntegerMaxValue() returns (res: Integer)
    ensures res.value == int32MaxValue
}
  
module {:extern "java.lang"} JavaLang {

  class {:extern "Integer" } Integer {
    ghost var value: int
    // Would be nice to have an ensures here that equates it to 2147483647
    // So we would not need Interop.int32MaxValue
    // Sadly this maps to MAX_VALUE() (note the incorrect parenthesis)
    // static const {:extern "MAX_VALUE"} MaxValue: Integer 
  }

}
module {:extern "java.util"} JavaRest {
  import opened JavaLang
  import opened Interop
  
  class {:extern "Random" } JavaRandom {
    constructor {:extern} ()
    
    method {:axiom} {:extern "nextInt"} Next(bound: Integer) returns (r: Integer)
      ensures 0 <= r.value && r.value < bound.value
  }
}