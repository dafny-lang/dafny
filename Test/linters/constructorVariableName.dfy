// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module BoatColor {
  datatype Color = ShadesofBlue(x: nat) | Yellow | White()
  method Boat(color: Color) {
    match color {
      case Yellow => print "first";
      case GreyScale => print "second"; 
      case White => print "third";
    }
  }
}

module CarColor {
  datatype Color = Red | GreyScale(x: nat) | Black()
  datatype T = GreyScale(x: nat) | Black()
  method MaybeWarning(color: Color) {
  match color {
    case GreyScale => print "first";
    case Red => print "second";
    case Black => print "third"; 
  }
  }
  method M(t: T) { 
  match t
    case GreyScale => print "A";
    case Black => print "B";
  }
  method MonochromaticMethod(c: Color) returns (x: bool) {
  return match c
    case GreyScale => true
    case Black => false;
  }
  function method MonochromaticFunction(c: Color) : bool {
  match c
    case GreyScale => true
    case Black => false      
  }
  method MonochromaticMethodloop(c: Color) returns (x: bool)  {
  var test := false;
  while test    
  {
      test := match c
        case GreyScale => true
        case Black => true     
        case anythingElse => false;
  }
  return false; 
  } 
}
 


