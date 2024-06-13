

function P(): bool {
  true
}

blind method Foo() {
  if (*) {
    reveal P();
    assert P();
  } else {
    assert P(); // error
  }
  var x := Bar();
  if (*) {
    reveal Bar();
    assert x;
  } else {
    assert x; // error
  }
  assert x;
}

method Bar() returns (x: bool) 
  ensures x 
