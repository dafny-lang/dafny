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
  case true =>
    var n := d.(y := 2.7, x := 3);
    assert n.A?;
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
  // Datatype field update works as follows:
  // 0- The fields given in the update must uniquely determine a constructor.
  //    The result will be of this constructor.
  // 1- For any pair "f := E" given in the update, the field "f" of the result will
  //    have the value "E".
  // 2- For any field "f" that is not given in the update "E.(x := X, y := Y, ...)",
  //    "E" must be a value with an "f" field and the value of "f" in the result will
  //    be "E.f".
  // Note, in point 2, the requirement that "E" have an "f" field is satisfied
  // if "E" is constructed by the same constructor as is determined in point 0.
  // However, it is also possible to satisfy this requirement if "f" is a shared
  // destructor and "E" is of a constructor that has that shared field.
  // Note also, that a degenerate case of the update expression is that all fields
  // of the by-point-0 determined constructor are given explicitly.  In that case,
  // the source of the update (that is, the "E" in "E.(...)") can be any value.
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

datatype Klef =
  | C0(0: int, 1: int, 2: int, c0: int)
  | C1(1: int, 2: int, 3: int, c1: int)
  | C2(2: int, 3: int, 0: int, c2: int)
  | C3(3: int, 0: int, 1: int, c3: int)

method TroubleKlef(k: Klef) returns (k': Klef)
  ensures k'.C3?
{
  if
  case k.C1? || k.C3? =>
    k' := k.(0 := 100, c3 := 200);  // makes a C3
    assert k' == C3(k.3, 100, k.1, 200);
  case true =>
    k' := k.(0 := 100, c3 := 200);  // error (x2): k might not have .1 and .3
}
