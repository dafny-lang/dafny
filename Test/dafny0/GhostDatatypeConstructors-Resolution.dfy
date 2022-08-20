// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Types {
  datatype XY =
    | {:hello} D0(x: int)
    | ghost {:bye} G0(y: bool)
    | ghost G1(y: bool, z: real, w: char)
    | {:yep} D1(z: real)

  datatype Wrapper<A> = Wrapper(A)
}

module Ghost {
  import opened Types

  method M0(xy: XY) {
    var x := xy.D0? && xy.x == 3;
    ghost var y := xy.G0? && xy.y;
    var yy;
    yy := xy.G0? && xy.y; // error: RHS is ghost, but LHS is not
  }

  method M1(xy: XY)
    requires xy.G1?
  {
    // Even though the verifier will forbid use of .y and .w in compiled contexts,
    // the resolver allows them.
    var y, z, w;
    y := xy.y;
    w := xy.w;
    z := xy.z;
  }

  method M2(ghost xy: XY)
    requires xy.G1?
  {
    var y, z, w;
    y := xy.y; // error: RHS is ghost, but LHS is not
    w := xy.w; // error: RHS is ghost, but LHS is not
    z := xy.z; // error: RHS is ghost, but LHS is not
  }
  }

module {:options "/functionSyntax:4"} Match {
  import opened Types

  method M0(xy: XY) returns (r: int) {
    match xy
    case _ => r := 0;
  }

  method M1(xy: XY) returns (r: int) {
    match xy
    case _ =>
  }

  method M2(w: Wrapper<XY>) returns (r: int) {
    match w
    case Wrapper(_) => r := 0;
  }

  method M3(w: Wrapper<XY>) returns (r: int) {
    match w
    case Wrapper(_) => r := 0;
  }

  method M4(w: Wrapper<XY>) returns (r: int) {
    match w
    case _ => r := 0;
  }

  method P0(xy: XY) returns (r: int) {
    // the following match statement is ghost, because it mentions a constructor of type XY
    match xy
    case D0(_) =>
    case _ => r := 0; // error: assignment to r in a ghost context
  }

  method P1(xy: XY) returns (r: int) {
    // the following match statement is ghost, because it mentions a constructor of type XY
    match xy
    case D0(_) =>
    case _ =>
  }

  method P2(w: Wrapper<XY>) returns (r: int) {
    match w
    case Wrapper(_) => r := 0;
  }

  method P3(w: Wrapper<XY>) returns (r: int) {
    // the following match statement is ghost, because it mentions a constructor of type XY
    match w
    case Wrapper(D0(_)) =>
    case Wrapper(_) => r := 0; // error: assignment to r in a ghost context
  }

  function F0(xy: XY): int {
    match xy
    case _ => 0
  }

  ghost function F1(xy: XY): int {
    match xy
    case _ => 0
  }

  function F2(w: Wrapper<XY>): int {
    match w
    case Wrapper(_) => 0
  }

  function F3(w: Wrapper<XY>): int {
    match w
    case Wrapper(_) => 0
  }

  function F4(w: Wrapper<XY>): int {
    match w
    case _ => 0
  }

  function G0(xy: XY): int {
    match xy
    case D0(_) => 0 // error: cannot match on XY constructor in a compiled context
    case _ => 0
  }

  ghost function G1(xy: XY): int {
    // the following match expression is ghost, because it mentions a constructor of type XY
    match xy
    case D0(_) => 0
    case _ => 0
  }

  function G2(w: Wrapper<XY>): int {
    match w
    case Wrapper(_) => 0
  }

  function G3(w: Wrapper<XY>): int {
    match w
    case Wrapper(D0(_)) => 0 // error: cannot match on XY constructor in a compiled context
    case Wrapper(_) => 0
  }
}

module EqualitySupport {
  import opened Types

  method M(xy: XY) returns (a: int) {
    if xy == xy { // this is okay, because the "if" statement is ghost
    }

    if xy == xy { // error: XY does not support equality
      a := 3;
    }
  }
}

module {:options "/functionSyntax:4"} Constructors {
  import opened Types

  method M0() returns (xy0: XY, ghost xy1: XY) {
    xy0 := D0(2);
    xy0 := D1(2.0);
    xy0 := G0(true); // error: G0 is a ghost constructor

    xy1 := D0(2);
    xy1 := D1(2.0);
    xy1 := G0(true);
  }

  method M1() returns (xy0: XY, ghost xy1: XY) {
    var a := D0(2);
    var b := D1(2.0);
    var c := G0(true); // this makes c auto-ghost

    xy0 := a;
    xy0 := b;
    xy0 := c; // error: RHS is ghost
    xy1 := a;
    xy1 := b;
    xy1 := c;
  }

  function F(b: bool): XY {
    if b then
      D0(2)
    else
      G0(true) // error: G0 is a ghost constructor
  }
}
