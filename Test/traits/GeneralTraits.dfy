// RUN: %exits-with 2 %dafny /compile:0 /generalTraits:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Tests {
  trait Parent { }

  datatype Dt extends Parent = Blue | Red

  type Abstract extends Parent

  method M(d: Dt, a: Abstract) {
    var p: Parent;
    p := d;
    p := a;
  }
}

module BadObjectExtensions {
  trait RefParent extends object { }
  datatype RefDt extends RefParent = Grey | Orange // error: datatype cannot extend object
  type RefAbstract extends RefParent // error: abstract type cannot extend object
}
