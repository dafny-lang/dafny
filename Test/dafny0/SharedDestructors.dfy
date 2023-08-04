// RUN: %exits-with 4 %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
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
    var n := d.(y := 2.7, x := 3);  // error: d must be constructed by A
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
  // A datatype field update "E.(x := X, y := Y, ...)" works as follows:
  //
  // 0- Expression "E" must be of some (inductive or co-inductive) datatype, say
  //    "D". The result of the update will have type "D".
  //
  // 1- The names "x", "y", ... must be destructors (aka members or fields) of
  //    "D". Duplicate names are not allowed. For each pair "x := X", the type
  //    of expression "X" must be assignable to field "x".
  //
  // 2- A constructor of "D" that has all the fields "x", "y", ... is called a
  //    _candidate result constructor_. The result of the update will be created
  //    by one of the candidate result constructors. If there is no candidate
  //    result constructor, then a resolution-time error is reported. A resolution-time
  //    error is also reported if a candidate result constructor does not name
  //    all of its parameters.
  //
  // 3- The _legal source constructors_ are the candidate result constructors.
  //    Let "C" denote the constructor that created "E". The verifier will check
  //    that "C" is among the legal source constructors. The result of the update
  //    will be created using constructor "C".
  //
  // 4- For any pair "x := X" given in the update, the field "x" of the result will
  //    have the value "X".
  //
  // 5- For any field "f" of "C" that is not given in the update, the value of "f"
  //    in the result will be "E.f". (Note that "E.f" is defined, since "E" is
  //    constructed by "C".)
  if
  case true =>
    // make a PP
    y' := y.(a := 10);  // error: y must be constructed by PP
  case y.QQ? =>
    // make a QQ
    y' := y.(b := 10);
  case true =>
    // make an RR
    y' := y.(c := 10, d := 20);  // error: y must be an RR
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
  case k.C3? =>
    k' := k.(0 := 100, c3 := 200);  // makes a C3
    assert k' == C3(k.3, 100, k.1, 200);
  case true =>
    k' := k.(0 := 100, c3 := 200);  // error: k should have been constructed by C3
}

datatype Many =
  | Ma0(x: int)
  | Ma1(u: int, fj: int)
  | Ma2(x: int, y: int)
  | Ma3(x: int, z: int)
  | Ma4(x: int, u: int)
  | Ma5(x: int, y: int)

method TestMany(m: Many) returns (r: Many)
{
  if
  case true =>
    r := m.(x := 3, y := 4);  // error: m is not known to be Ma2 or Ma5
  case m.Ma2? || m.Ma5? =>
    r := m.(x := 3, y := 4);  // error: m is not known to be Ma2 or Ma5
    assert r.x == 3;
    assert r.y == 4;
    assert r.Ma2? || r.Ma5?;
    assert r.Ma2?;  // error: it could also be Ma5
  case m.Ma4? =>
    r := m.(u := 8);
    assert m.Ma4?;
    assert r.x == m.x;
  case !m.Ma1? =>
    r := m.(x := 5);
    assert !r.Ma1?;
    assert m.Ma4? ==> r.Ma4?;
}
