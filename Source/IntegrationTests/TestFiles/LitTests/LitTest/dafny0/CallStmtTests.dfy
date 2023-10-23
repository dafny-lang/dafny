// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module M0 {
  method testing1(t: int)
 {
    t := m(); // error: should be checked at the Dafny level, not fall to Boogie.
  }

  method m() returns (r: int)
  {
    return 3;
  }
}

module M1 {
  method testing2()
  {
    var v;
    v := m2(); // error: v needs to be ghost because r is.
  }

  method m2() returns (ghost r: int)
  {
    r := 23;
  }
}
