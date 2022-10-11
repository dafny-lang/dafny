// RUN: %dafny_0 -compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Dummy {
  const i: int
  constructor(i: int) {
    this.i := i;
  }
}

class NoError {
  const a: int
  const a2: int
  const a3: int
  const b: int
  const c: int
  const d: Dummy
  const e: array<int>

  constructor() {
    a := 3;
    if a == 3 {
      a2 := 1;
    } else {
      a2 := 2;
    }
    match a2 {
      case 2 =>
        a3 := a;
      case _ =>
        a3 := a + 1;
    }
    b := a3 + 1;
    c := a2;
    d := new Dummy(c);
    e := new int[b];
  }
}

class AlternativeError {
  const a: int
  const a2: int
  const b: int
  const b2: int

  constructor() {
    if true {
      a := 1;
    }
    b := a; // Error here
    match true {
      case true =>
        a2 := 1;
      case false =>
    }
    b2 := a2; // Error here
  }
}

class LoopError {
  const a: int
  const a2: int
  const a3: int
  const a4: int

  constructor() {
    while true {
      a := 1; // Error here
    }
    while {
      case true =>
        a2 := 1; // Error here
    }
    if {
      case true =>
        a3 := 1; // Error here
    }
    /*forall x: nat {
      a4 := 1; // Error here
    }*/
  }
}

class SecondInitializationError {
  const a := b + b
  const b: int

  constructor (x: int) {
    var k := a; // Error here
    print a, "\n";
    b := x;
    assert k == a;
    print a, "\n";
    if k != a {
      var y := 5 / 0;
    }
  }
}

class RecursiveError {
  const a: int := b
  const b: int

  constructor () {
    b := a + 1; // Error here
    new;
    assert false;
  }
}

method Main() {
  var c := new SecondInitializationError(5);
  var d := new RecursiveError();
}