// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Types {
  datatype XY =
    | D0(x: int)
    | ghost G0(y: bool)
    | ghost G1(y: bool, z: real, w: char)
    | D1(z: real, y: bool)

  class Cl { }

  datatype G = G(Cl)
}

module Ghost {
  import opened Types

  method M0(xy0: XY, xy1: XY) returns (r: int, ghost s: int)
    requires xy0.D0? || xy0.D1?
  {
    if xy0.D1? {
      r := 3;
    }

    if xy1.D1? { // fine, since this is a ghost context
      s := 3;
    }

    if xy1.D1? { // error: xy1 might be of a ghost variant
      r := 3;
    }
  }

  method M1(xy: XY)
    requires xy.G1?
  {
    var x, y, z;
    if
    case true =>
      x := xy.x; // error: xy is not a D0
    case true =>
      y := xy.y; // error: compiled context cannot read .y
    case true =>
      z := xy.z; // error: compiled context cannot read .w of a G1
  }

  method M2(xy: XY)
    requires xy.G1?
  {
    ghost var x, y, z, w;
    if
    case true =>
      x := xy.x; // error: xy is not a D0
    case true =>
      y := xy.y;
    case true =>
      w := xy.w;
    case true =>
      z := xy.z;
  }

  method M3(xy: XY)
    requires xy.D1?
  {
    ghost var x, z;
    if
    case true =>
      x := xy.x; // error: xy is not a D0
    case true =>
      z := xy.z;
  }

  method Update0(xy: XY) returns (r: XY)
    requires xy.G1?
  {
    if
    case true =>
      r := xy.(x := 2); // error: xy is not a D0
    case true =>
      r := xy.(y := true); // error: compiled context cannot update .y
  }

  method Update1(xy: XY) returns (r: XY)
    requires xy.G1?
  {
    if
    case true =>
      r := xy.(z := 2.2); // error: compiled context cannot update .z of a G1
    case true =>
      r := xy.(z := 2.2, y := true); // error: compiled context cannot update .z/.y of a G1
  }

  method Update2(xy: XY) returns (ghost r: XY)
    requires xy.G1?
  {
    if
    case true =>
      r := xy.(x := 2); // error: xy is not a D0
    case true =>
      r := xy.(y := true);
    case true =>
      r := xy.(w := 'w');
    case true =>
      r := xy.(z := 2.2);
    case true =>
      r := xy.(z := 2.2, y := true);
    case true =>
      r := xy.(z := 2.2, w := 'w', y := true);
  }
}

module Initialization {
  import opened Types

  method M0() returns (xy: XY) { // no problem not explicitly initializing xy
  }

  method M1() returns (g: G) {
  } // error: g requires initialization

  method M2() returns (ghost g: G) {
  } // error: g requires initialization
}

module Members {
  datatype DM = ghost A(x: int) | B(x: int, y: int) | C(y: int, z: int)
  {
    const n := 100

    function F(): int {
      3
    }

    method M() returns (r: int) {
      r := 3;
      if * {
        r := r + n; // it's fine to use the field "n"
      }
    }

    method Bad() returns (r: int) {
      if C? { // error: cannot ask about C? since ghost variant A? is a possibility
        r := z;
      } else {
        r := x;
      }
    }

    method Redeemed() returns (r: int)
      requires !A?
    {
      if C? {
        r := z;
      } else {
        r := x;
      }
    }
  }
}

module {:options "/functionSyntax:4"} EqualitySupport {
  import opened Types

  method M(xy: XY, selector: int) returns (a: int)
  {
    if xy == xy { // this is okay, because the "if" statement is ghost
    }

    if xy == xy { // error: XY only partially supports equality
      a := 3;
    }
  }

  method N(xy: XY, selector: int) returns (a: int)
    requires xy.D0? || xy.D1?
  {
    if xy == xy { // fine
      a := 3;
    }
  }

  datatype Enum = ghost EnumA | EnumB
  {
    predicate P() {
      this != EnumB // error: XY only partially supports equality
    }

    predicate Q()
      requires EnumB?
    {
      this != EnumB
    }

    predicate R()
      requires !EnumA?
    {
      this != EnumB
    }
  }
}
