// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// ---------- compiled variables/fields ----------

module GhostWitness {
  type Five = x: int | x == 5 ghost witness 5

  class ContainsFive {
    var five: Five

    constructor () {
      five := *;
    } // error: five not defined
  }

  method M() {
    var five: Five := *;
    var c := new ContainsFive();

    if
    case true =>
      print five, "\n"; // error: five used before defined
    case true =>
      var x :=
        var f: Five := five; // error: five used before defined
        assert f == 5;
        if f == 5 then 200 else 200/0;
    case true =>
      print c.five, "\n";
  }
}

module CompiledWitness {
  type Five = x: int | x == 5 witness 5

  class ContainsFive {
    var five: Five

    constructor () {
      five := *;
    }
  }

  method M() {
    var five: Five := *;
    var c := new ContainsFive();

    if
    case true =>
      print five, "\n";
    case true =>
      var x :=
        var f: Five := five;
        assert f == 5;
        if f == 5 then 200 else 200/0;
    case true =>
      print c.five, "\n";
  }
}

module NoWitness {
  type Five = x: int | x == 5 witness *

  class ContainsFive {
    var five: Five

    constructor () {
      five := *;
    } // error: five not defined
  }

  method M() {
    var five: Five := *;
    var c := new ContainsFive();

    if
    case true =>
      print five, "\n"; // error: five used before defined
    case true =>
      var x :=
        var f: Five := five; // error: five used before defined
        assert f == 5;
        if f == 5 then 200 else 200/0;
    case true =>
      print c.five, "\n";
  }
}

// ---------- ghost variables/fields ----------

module XGhostWitness {
  type Five = x: int | x == 5 ghost witness 5

  class ContainsFive {
    ghost var five: Five

    constructor () {
      five := *;
    }
  }

  method M() returns (ghost g: int) {
    g := 0;
    ghost var five: Five := *;
    var c := new ContainsFive();

    if
    case true =>
      g := five;
    case true =>
      ghost var x :=
        var f: Five := five;
        assert f == 5;
        if f == 5 then 200 else 200/0;
    case true =>
      g := c.five;
  }
}

module XCompiledWitness {
  type Five = x: int | x == 5 witness 5

  class ContainsFive {
    ghost var five: Five

    constructor () {
      five := *;
    }
  }

  method M() returns (ghost g: int) {
    g := 0;
    ghost var five: Five := *;
    var c := new ContainsFive();

    if
    case true =>
      g := five;
    case true =>
      ghost var x :=
        var f: Five := five;
        assert f == 5;
        if f == 5 then 200 else 200/0;
    case true =>
      g := c.five;
  }
}

module XNoWitness {
  type Five = x: int | x == 5 witness *

  class ContainsFive {
    ghost var five: Five

    constructor () {
      five := *;
    } // error: five not defined
  }

  method M() returns (ghost g: int) {
    g := 0;
    ghost var five: Five := *;
    var c := new ContainsFive();

    if
    case true =>
      g := five; // error: five used before defined
    case true =>
      ghost var x :=
        var f: Five := five; // error: five used before defined
        assert f == 5;
        if f == 5 then 200 else 200/0;
    case true =>
      g := c.five;
  }
}
