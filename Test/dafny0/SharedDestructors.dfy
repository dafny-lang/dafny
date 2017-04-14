// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Dt =
  | A(x: int, y: real)
  | B(h: MyClass, x: int)
  | C(y: real)
  | D(u: int, y: real, v: bool)

class MyClass { }

method M(d: Dt) returns (r: int, s: real)
{
  if
  case true =>
    r := d.x;  // error: d might not have a member .x (2 names in error msg)
  case d.A? =>
    r := d.x;
  case d.B? =>
    r := d.x;
  case d.C? =>
    r := d.x;  // error: d definitely does not have a member .x
  case d.B? =>
    s := d.y;  // error: d does not have a member .y (3 names in error msg)
  case !d.B? =>
    s := d.y;
  case d.D? || d.C? =>
    s := d.y;
  case true =>
    var h := d.h;  // error: d might not have a member .h (1 name in error msg)
  case d.B? =>
    var h := d.h;
}

datatype Record = Record(t: int)
datatype Shared = AA(id: int, a: real, c: real) | BB(id: int, b: real)

method N(r: Record, sh: Shared, bb: Shared) returns (r': Record, f: real, sh': Shared)
  requires bb.BB?
{
  r' := r.(t := r.t + sh.id);
  if sh.AA? {
    f := sh.a;
    sh' := sh.(a := bb.b + 100.2);
  } else {
    sh' := AA(r.t, r.t as real, 0.0);
    if * {
      f := sh.a;  // error: sh does not have a member .a
    }
  }
  if * {
    sh' := sh'.(a := bb.b);
  } else {
    sh' := sh.(a := bb.b);  // error: sh might not have a member .a
  }
}

datatype Quirky = PP(id: int, a: int) | QQ(b: int, id: int) | RR(id: int, c: int, d: int)

method UpdateA(y: Quirky) returns (y': Quirky)
{
  // The semantics of datatype field update is somewhat quirky.  It's perhaps a design
  // bug, but here is what it requires and what it does:
  // - Each field given must be a non-shared destructor.  That is, each field mentioned
  //   must be a destructor in a unique constructor.  (An alternative to this design
  //   would be to just insist that the intersection of the constructors that contain
  //   the given fields must be a single constructor.)
  //   This unique constructor is the constructor that will be used for the result.
  // - Every field "g" of the chosen constructor must either be given in the update
  //   expression or be available in the source expression.  This does not necessarily
  //   mean that the source expression must already be of the chosen constructor; it
  //   suffices that every such "g" is available in all of the constructors.  A special
  //   case of this is that there is no "g", in which case the value of the source
  //   expression does not matter at all.
  if
  case true =>
    // make a PP, get .id from anywhere
    y' := y.(a := 10);
  case true =>
    // make a QQ, get .id from anywhere
    y' := y.(b := 10);
  case true =>
    // make an RR, get .id from anywhere
    y' := y.(c := 10, d := 20);
  case y.RR? =>
    // make an RR, get .id and .d from y
    y' := y.(c := 10);
  case true =>
    // make an RR, but where does .d come from?
    y' := y.(c := 10);  // error: this would require y to be an RR
}
