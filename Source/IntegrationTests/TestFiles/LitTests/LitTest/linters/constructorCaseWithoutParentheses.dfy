// RUN: %exits-with 2 %verify --warn-missing-constructor-parentheses "%s" --allow-warnings > "%t"
// RUN: %diff "%s.expect" "%t"

/* These tests were originally designed to test --warn-missing-constructor-parentheses, which reported
 * a warning when a nullary constructor in a match-case did not include parentheses.
 *
 * In the new resolver, that option has been superseded by reporting an error if a non-nullary
 * constructor is used without arguments. The use of the --warn-missing-constructor-parentheses option
 * in this test is thus not necessary.
 */

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
  function Foo(value: Identity<Colors>): bool {
    match value {
      case Identity(Yellow()) => true
      case Identity(Blue) => false
    }
  }
  method MonochromaticMethod(c: Color) returns (x: bool) {
    return match c
      case ShadesOfGray => true // error: needs arguments
      case Green => true
      case anythingElse => false;
  }
  function MonochromaticFunction(c: Color) : bool {
    match c
      case ShadesOfGray => true // error: needs arguments
      case Green => true
      case anythingElse => false      
  }
  method MonochromaticMethodloop(c: Color) returns (x: bool)  {
    var test := false;
    while test    
    {
       test := match c
         case ShadesOfGray => true // error: needs arguments
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
  function Foo(value: Identity<Colors>): bool {
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
  function MonochromaticFunction(c: Color) : bool {
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



