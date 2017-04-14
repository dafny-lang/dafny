// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Module0 {
  datatype Dt =
    | A(x: int, y: real)
    | B(h: MyClass, x: int)
    | C(y: real)
    | D(u: int, y: real, v: bool)

  class MyClass { }

  method Update(d: Dt) returns (d': Dt)
  {
    if d.A? {
      d' := d.(x := 6);  // error: the destructor to be updated must be uniquely named
    } else if d.B? {
      d' := d.(h := null);
    } else {
      d' := d.(y := 0.0);  // error: the destructor to be updated must be uniquely named
    }
  }
}

module Module1 {
  type SKt = Kt

  datatype Kt =
    Kt0(x: int) |
    Kt1(ghost x: int) |  // error: duplicated destructors must agree on ghost/non-ghost
    Kt2(ghost g: int) |
    Kt3(g: int) |  // error: duplicated destructors must agree on ghost/non-ghost
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
