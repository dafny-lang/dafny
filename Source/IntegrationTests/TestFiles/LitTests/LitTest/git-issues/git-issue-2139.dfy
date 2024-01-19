// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  datatype T = T(T, T)
  {
    ghost predicate P() {
      match this
      case T(0, 1) => false // error (x2): neither constant pattern of constructor pattern has the right type
    }
  }
  
  method M() {
    var tok := (0, 0);
    match tok {
      case "B" => // error: "B" is not of type (int, int)
      case _ => 
    }
  }
}

module B {
  datatype T = T(T, T) // error (masked by other errors in module A): cycle prevents instances
}
