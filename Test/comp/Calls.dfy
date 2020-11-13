// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function method F(x: int, y: bool): int {
  x + if y then 2 else 3
}

method A0(x: int, y: bool) {
  return;
}

method A1(x: int, y: bool) returns (a: int) {
  return a;
}

method A2(x: int, y: bool) returns (a: int, b: bool) {
  return a, b;
}

method A3(x: int, y: bool) returns (a: int, b: bool, c: int) {
  var u;
  if x == 3 {
    u := c;
  } else if x == 4 {
    u := c + 0;
  } else {
    u := c + 0 + 0;
  }
  u := 1 * u;
  {
    var y := 65;
    u := 0 + u;
  }
  return a, b, u;
}

method Main()
{
  var w, a, b, c, d, e, f;
  w := F(2, false);
  A0(2, false);
  a := A1(2, false);
  b, c := A2(2, false);
  d, e, f := A3(2, false);
  print w, " ", a, " ", b, " ", c, " ", d, " ", e, " ", f, "\n";

  FunctionValues.Test();
}

module FunctionValues {
  method Test() {
    var c := new Class(5);
    var color := Red;
    var nt: NT := 5;
    ApplyAndPrint(c.F);
    ApplyAndPrint(c.G);
    ApplyAndPrint(color.F);
    ApplyAndPrint(color.G);
    ApplyAndPrint(nt.F);
    ApplyAndPrint(nt.G);
    print "\n";
    // test variable capture
    var x0, x1, x2, x3, x4, x5 := c.F, c.G, color.F, color.G, nt.F, nt.G;
    c := new Class(2);
    color, nt := Blue, 2;
    print x0(), " ", x1(), " ", x2(), " ", x3(), " ", x4(), " ", x5(), "\n";
  }

  method ApplyAndPrint(f: () -> int) {
    print f(), " ";
  }

  class Class {
    const x: int
    constructor (x: int) { this.x := x; }
    function method F(): int { x }
    static function method G(): int { 3 }
  }

  datatype Color = Red | Green | Blue {
    function method F(): int { if this == Red then 5 else 2 }
    static function method G(): int { 3 }
  }

  newtype NT = x | 0 <= x < 15 {
    function method F(): int { this as int }
    static function method G(): int { 3 }
  }
}
