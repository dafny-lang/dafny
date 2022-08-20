// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Types {
  datatype XY =
    | {:hello} D0(x: int)
    | ghost {:bye} G0(y: bool)
    | ghost G1(y: bool, z: real, w: char)
    | {:yep} D1(z: real)
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

module EqualitySupport {
  import opened Types

  method M3(xy: XY) returns (a: int) {
    if xy == xy { // this is okay, because the "if" statement is ghost
    }

    if xy == xy { // error: XY does not support equality
      a := 3;
    }
  }
}
