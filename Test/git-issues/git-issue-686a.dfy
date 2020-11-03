// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Color = Blue | Red

function method Foo(c: Color): int {
  match c
  case Blue => 4
  case Blue =>  // warning: redundant branch
    assert doesNotExist == TotallyBogus + (3 && true);  // ERROR: resolver issues correct complaints, even though this case is redundant
    5
  case Red => 6
}

method Moo(c: Color) returns (x: int) {
  match c
  case Blue =>
  case Blue =>  // warning: redundant branch
    doesNotExist := TotallyBogus + 3 && true;  //  ERROR: resolver issues correct complaints, even though this case is redundant
  case Red =>
}

