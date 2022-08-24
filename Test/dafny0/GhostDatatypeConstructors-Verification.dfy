// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Types {
  datatype XY =
    | {:hello} D0(x: int)
    | ghost {:bye} G0(y: bool)
    | ghost G1(y: bool, z: real, w: char)
    | {:yep} D1(z: real)

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
    var x, y, z, w;
    if
    case true =>
      x := xy.x; // error: xy is not a D0
    case true =>
      y := xy.y; // error: compiled context cannot read .y
    case true =>
      w := xy.w; // error: compiled context cannot read .w
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
    case true =>
      r := xy.(w := 'w'); // error: compiled context cannot update .w
  }

  method Update1(xy: XY) returns (r: XY)
    requires xy.G1?
  {
    if
    case true =>
      r := xy.(z := 2.2); // error: compiled context cannot update .z of a G1
    case true =>
      r := xy.(z := 2.2, y := true); // error: compiled context cannot update .z/.y of a G1
    case true =>
      r := xy.(z := 2.2, w := 'w', y := true); // error: compiled context cannot update .z/.w/.y of a G1
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

module {:options "/functionSyntax:4"} Regressions {
  predicate P(x: int)

  method M0(ghost y: int) returns (r: int)
    requires P(y)
  {
    var gg := (var x :| P(x); x) == 0; // error: x might not be unique (gg is considered non-ghost)
    if gg {
      r := 0;
    }
  }

  method M1(ghost y: int) returns (r: int)
    requires P(y)
  {
    if (var x :| P(x); x) == 0 { // error: x might not be unique
      r := 0;
    }
  }

  method M2(ghost y: int)
    requires P(y)
  {
    // the following "if" statement is ghost
    if (var x :| P(x); x) == 0 {
    }
  }

  method M3(y: int) returns (r: int)
    requires P(y)
  {
    if
    case 2 < y =>
      r := 0;
    case (var x :| P(x); x) == 0 => // error: x might not be unique
    case true =>
  }

  method M4(ghost y: int)
    requires P(y)
  {
    while (var x :| P(x); x) == 0 { // error: x might not be unique
      break;
    }
  }

  method M5(y: int)
    requires P(y)
  {
    while
    case 2 < y =>
      break;
    case (var x :| P(x); x) == 0 => // error: x might not be unique
      break;
    case true =>
      break;
  }

  method M6(ghost y: int) returns (r: int)
    requires P(y)
  {
    for i := if (var x :| P(x); x) == 0 then 3 else 2 to 25 { // error: x might not be unique
      r := 0;
    }
  }

  method M7(ghost y: int) returns (r: int)
    requires P(y)
  {
    for i := 0 to if (var x :| P(x); x) == 0 then 3 else 2 { // error: x might not be unique
      r := 0;
    }
  }

  method M8(a: array<int>, y: int)
    requires P(y)
    modifies a
  {
    forall i | 0 <= i < if (var x :| P(x); x) == 0 then a.Length else 0 { // error: x might not be unique
      a[i] := 0;
    }
  }

  method M9(y: int) returns (r: int)
    requires P(y)
  {
    match if (var x :| P(x); x) == 0 then 3 else 0 // error: x might not be unique
    case 0 =>
    case 1 =>
      r := 0;
    case _ =>
  }

  method M10(y: int)
    requires P(y)
  {
    // Here, the entire match statement is ghost
    match if (var x :| P(x); x) == 0 then 3 else 0
    case 0 =>
    case 1 =>
    case _ =>
  }

  datatype Color = Red | Blue | Green

  method M11(c: Color, y: int) returns (r: int)
    requires P(y)
  {
    match if (var x :| P(x); x) == 0 then c else c // error: x might not be unique
    case Red =>
    case Green =>
      r := 0;
    case Blue =>
  }

  method M12(c: Color, y: int)
    requires P(y)
  {
    // Here, the entire match statement is ghost
    match if (var x :| P(x); x) == 0 then c else c
    case Red =>
    case Green =>
    case Blue =>
  }
}
