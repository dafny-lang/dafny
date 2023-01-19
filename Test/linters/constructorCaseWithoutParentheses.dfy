// RUN: %baredafny verify %args --warn-missing-constructor-parentheses "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module WithWarning {
  datatype Color = Red | Green | ShadesOfGray(nat)
  datatype Identity<T> = Identity(value: T)
  datatype Colors = Yellow | Blue
  datatype T = A | B
  method M(t: T) { 
    match t
      case A => print "A";
      case B => print "B";
  }
  function method Foo(value: Identity<Colors>): bool {
    match value {
      case Identity(Yellow()) => true
      case Identity(Blue) => false
    }
  }
  method MonochromaticMethod(c: Color) returns (x: bool) {
    return match c
      case ShadesOfGray => true
      case Green => true
      case anythingElse => false;
  }
  function method MonochromaticFunction(c: Color) : bool {
    match c
      case ShadesOfGray => true
      case Green => true
      case anythingElse => false      
  }
  method MonochromaticMethodloop(c: Color) returns (x: bool)  {
    var test := false;
    while test    
    {
       test := match c
         case ShadesOfGray => true
         case Green => true      
         case anythingElse => false;
    }
    return false; 
  }
   
}

module WithoutWarning {
  datatype Color = Red | Green | ShadesOfGray(nat)
  datatype Identity<T> = Identity(value: T)
  datatype Colors = Yellow | Blue
  datatype T = A | B
    method M(t: T) { 
      match t
        case A() => print "A";
        case B() => print "B";
    }
  function method Foo(value: Identity<Colors>): bool {
    match value {
      case Identity(Yellow()) => true
      case Identity(Blue()) => false
    }
  }
  method MonochromaticMethod(c: Color) returns (x: bool) {
        return match c
          case ShadesOfGray(_) => true
          case Green() => true
          case anythingElse => false;
  }
  function method MonochromaticFunction(c: Color) : bool {
        match c
          case ShadesOfGray(_) => true
          case Green() => true
          case anythingElse => false
  }
  method MonochromaticMethodloop(c: Color) returns (x: bool)  {
        while false {
          x := match c
              case ShadesOfGray(_) => true
              case Green() => true
              case anythingElse => false;
        }
      return false; 
  }
  method Main() {
        var x := MonochromaticMethod(Green); 
        print MonochromaticFunction(Green);
        var y := MonochromaticMethodloop(Green);
        print Foo(Identity(Blue));
      }
}



