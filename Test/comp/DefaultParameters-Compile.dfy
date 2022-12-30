// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" >> "%t"
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

function method F(x: int := 5): int { x }

method FF(w: int := x, x: int := F(), y: int := w + 1) {
  print w, " ", x, " ", y, "\n";
}

method GG(w: int := x, x: int := G(), y: int := w + 1) {
  print w, " ", x, " ", y, "\n";
}

function method G(x: int := 6): int { x }

