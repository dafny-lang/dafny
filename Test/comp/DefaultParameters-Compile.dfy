// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method M(x: int := 16) {
  print x, "\n";
}

class C {
  var data: int
  method M(x: int := data, y: int := x + 2) {
    print x, " ", y, "\n";
  }
}

datatype Color = Blue(x: int, y: int := x - 1) | Red(x: int, y: int := x + 1)

method Main() {
  M(12);
  M();
  var c := new C;
  c.data := 10;
  c.M(1, 2); // 1 2
  c.M(1); // 1 3
  c.M(y := 20); // 10 20
  c.data := 11;
  c.M(); // 11 13
  var c0, c1 := Blue(2), Red(3);
  print c0, " ", c1, "\n"; // Blue(2, 1) Red(3, 4)
  FF(); // 5 5 6
  GG(); // 6 6 7
}

function F(x: int := 5): int { x }

method FF(w: int := x, x: int := F(), y: int := w + 1) {
  print w, " ", x, " ", y, "\n";
}

method GG(w: int := x, x: int := G(), y: int := w + 1) {
  print w, " ", x, " ", y, "\n";
}

function G(x: int := 6): int { x }

