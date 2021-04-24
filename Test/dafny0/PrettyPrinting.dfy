// RUN: %dafny /dprint:- /env:0 /noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  method M()
}

module B refines A {
  method M ... {
    while true
    while true
      invariant true
      invariant true
    while true
      decreases 5
    while true
      modifies {}
    while ...
    while true
      ...
    while true {
      var u := 0;
    }
    var x := 10;
  }

  method P(a: array<int>)
    modifies a
  {
    forall i | 0 <= i < 100 {
      a[i] := 200;
    }
    forall i | 0 <= i < 100
      ensures true
    forall i | 0 <= i < 100
      ensures true
    {
    }
  }
}
