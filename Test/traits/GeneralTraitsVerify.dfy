// RUN: %exits-with 4 %dafny /compile:0 /traitsReferences:0 "%s" > "%t"
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

  method N(p: Parent) {
    if
    case true =>
      var d: Dt;
      d := p as Dt; // error: perhaps p isn't a Dt
    case true =>
      var a: Abstract;
      a := p as Abstract; // error: perhaps p isn't an Abstract
  }

  method P(p: Parent) {
    if
    case p is Dt =>
      var d: Dt;
      d := p as Dt;
    case p is Abstract =>
      var a: Abstract;
      a := p as Abstract;
    case true =>
  }
}
