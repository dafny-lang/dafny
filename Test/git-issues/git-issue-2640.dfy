// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:options "/functionSyntax:4"} CompilableExpressions {
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
