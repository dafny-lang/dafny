// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Color = Blue | Red

function method Foo(c: Color): int {
  match c
  case Blue => 4
  case Blue =>  // warning: redundant branch, not shown because of other resolution errors.
    assert doesNotExist == TotallyBogus + (3 && true);  // ERROR: resolver issues correct complaints, even though this case is redundant
    5
  case Red => 6
}

method Moo(c: Color) returns (x: int) {
  match c
  case Blue =>
  case Blue =>  // warning: redundant branch, not shown because of other resolution errors.
    doesNotExist := TotallyBogus + 3 && true;  //  ERROR: resolver issues correct complaints, even though this case is redundant
  case Red =>
}

datatype Bar = Bar(value: int)
function method Zoo(b: Bar, x: real): int requires b.value == 4 {
  match b
  case Bar(_) => 4
  case Bar(x) => assert x == 4; 5
}

method Coo(b: Bar) {
  var x: real;
  match b
  case Bar(_) =>
  case Bar(x) => print x+1;
}
