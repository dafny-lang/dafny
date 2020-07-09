datatype Color = Blue | Red
  
function method Foo(c: Color): int {
  match c
  case Blue => 4
  case Blue =>  // warning: redundant branch
    assert doesNotExist == TotallyBogus + (3 && true);  // BOGUS: there should be complaints about this line, but there aren't
    5
  case Red => 6
}

method Moo(c: Color) returns (x: int) {
  match c
  case Blue =>
  case Blue =>  // warning: redundant branch
    doesNotExist := TotallyBogus + 3 && true;  // BOGUS: there should be complaints about this line, but there aren't
  case Red =>
}

method Main() {
  var x := Moo(Red);
  print Foo(Red), " ", x, "\n";
}
