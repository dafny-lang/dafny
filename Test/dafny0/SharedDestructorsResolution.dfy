// RUN: %exits-with 2 %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Module0 {
  datatype Dt =
    | A(x: int, y: real)
    | B(h: MyClass, x: int)
    | C(y: real)
    | D(u: int, y: real, v: bool)
    | E(u: int, /*unnamed*/int)
  class MyClass { }

  method Update(d: Dt) returns (d': Dt)
  {
    if d.D? || d.E? {
      d' := d.(u := 6);  // error: a candidate result constructor (E) has unnamed fields
    } else if d.B? {
      d' := d.(h := null);
    } else {
      d' := d.(y := 0.0);
    }
    d' := d.(x := 100, h := null);
  }

  datatype Klef =
    | C0(0: int, 1: int, 2: int, c0: int)
    | C1(1: int, 2: int, 3: int, c1: int)
    | C2(2: int, 3: int, 0: int, c2: int)
    | C3(3: int, 0: int, 1: int, c3: int)

  method UK(k: Klef, x: int) returns (k': Klef)
  {
    k' := k.(2 := x, 3 := x, 0 := x);  // this makes a C2
    k' := k.(0 := x, 1 := x);  // ambiguous, but that's okay
    k' := k.(c0 := x, 3 := x);  // error: no constructor has both "c0" and "3"
    k' := k.(3 := x, c0 := x);  // error: ditto
    k' := k.(3 := x, 2 := x, c0 := x);  // error: no constructor has all these destructors
    k' := k.(3 := x, 2 := x, 1 := x, c0 := x);  // error: no constructor has all these destructors
    k' := k.(3 := x, 1 := x, 0 := x);  // this makes a C3
    k' := k.(1 := x, c3 := x);  // this makes a C3
    k' := k.(0 := x, 0 := x, 1 := x);  // error: c0 duplicate
    // multiples errors:
    k' := k.(C0? := x);  // error: C0? is not a destructor
    k' := k.(C0? := x, c0 := x);  // error: ditto
    k' := k.(c0 := x, c0 := x, c2 := x);  // error (2x): c0 duplicate, c2 never with c0
    k' := k.(c0 := x, c1 := x, c2 := x);  // error (2x): c1 and c2 never with c0
  }
}

module Module1 {
  type SKt = Kt

  datatype Kt =
    Kt0(x: int) |
    Kt1(ghost x: int) |  // (duplicated destructors must agree on ghost/non-ghost, but this is not report until a later pass; see Module2)
    Kt2(ghost g: int) |
    Kt3(g: int) |  // (duplicated destructors must agree on ghost/non-ghost, but this is not report until a later pass; see Module2)
    Kt4(k: Kt) |
    Kt5(k: SKt) |  // fine, because SKt and Kt are synonyms
    Kt6(k: S'Kt)  // fine, because S'Kt and Kt are synonyms

  datatype Lt =
    Lt0(x: int) |
    Lt1(x: real)  // error: duplicated destructors must agree on the type

  datatype Mt<A,B> =
    Mt0(x: A, y: A) |
    Mt1(x: A) |
    Mt2(y: B) | // error: duplicated destructors must agree on the type
    Mt3(arr: array<A>) |
    Mt4(arr: array<B>) |  // error: duplicated destructors must agree on the type
    Mt5(arr: array<object>) |  // error: duplicated destructors must agree on the type
    Mt6(sy: Syn<bool>) |
    Mt7(sy: Syn<MyTrait>) |  // fine, because Syn<bool> and Syn<MyTrait> are synonyms for the same thing
    Mt8(op: Opaque<int>) |
    Mt9(op: Opaque<bool>) |  // error: duplicated destructors must agree on the type
    Mt10(oop: Opaque<Opaque<B>>) |
    Mt11(oop: Opaque<Opaque<A>>) |  // error: duplicated destructors must agree on the type
    Mt12(ooi: Opaque<Opaque<int>>) |
    Mt13(ooi: Opaque<Opaque<Syn<real>>>)  // fine

  trait MyTrait { }

  type S'Kt = Kt

  type Syn<Unused> = int

  type Opaque<T>

  codatatype CoDt =
    | Co0(next: CoDt)
    | Co1(next: CoDt)
    | Co2(u: int)
    | Co3(a: int, b: int, u: real, v: real)  // error: type of 'u' does not agreee in Co2 and Co3

  datatype SameInOneCtor =
    | Same0(x: int, y: int, x: int)  // error: duplicate destructor name in the same constructor
    | Same1(y: int, y: int)  // error: duplicate destructor name in the same constructor
    | Same2(z: int, ghost z: bool)  // error: duplicate destructor name in the same constructor
}

module Module2 {
  datatype Kt =
    Kt0(x: int) |
    Kt1(ghost x: int) |  // error: duplicated destructors must agree on ghost/non-ghost
    Kt2(ghost g: int) |
    Kt3(g: int)  // error: duplicated destructors must agree on ghost/non-ghost
}
