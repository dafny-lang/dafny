// RUN: %exits-with 4 %dafny /typeSystemRefresh:1 /generalTraits:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Tests {
  trait Parent { }

  class Class extends Parent { }
  datatype Dt extends Parent = Blue | Red
  codatatype CoDt extends Parent = InfiniteBlue | InfiniteRed
  type Abstract extends Parent
  newtype MyInt extends Parent = int
  newtype MyConstrainedInt extends Parent = x | 0 <= x < 10

  method M(c: Class, d: Dt, co: CoDt, a: Abstract, mi: MyInt, mc: MyConstrainedInt) {
    var p: Parent;
    p := c;
    p := d;
    p := co;
    p := a;
    p := mi;
    p := mc;
  }

  method N(p: Parent) {
    if
    case true =>
      var x: Class;
      x := p as Class; // error
    case true =>
      var x: Dt;
      x := p as Dt; // error
    case true =>
      var x: CoDt;
      x := p as CoDt; // error
    case true =>
      var x: Abstract;
      x := p as Abstract; // error
/*    case true =>
      var x: MyInt;
      x := p as MyInt; // error
    case true =>
      var x: MyConstrainedInt;
      x := p as MyConstrainedInt; // error
*/  }

  method P(p: Parent) {
    if
    case p is Class =>
      var x: Class;
      x := p as Class;
    case p is Dt =>
      var x: Dt;
      x := p as Dt;
    case p is CoDt =>
      var x: CoDt;
      x := p as CoDt;
    case p is Abstract =>
      var x: Abstract;
      x := p as Abstract;
/*    case p is MyInt =>
      var x: MyInt;
      x := p as MyInt;
    case p is MyConstrainedInt =>
      var x: MyConstrainedInt;
      x := p as MyConstrainedInt;
*/    case true =>
  }
}
