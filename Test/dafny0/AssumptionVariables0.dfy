// RUN: %exits-with 2 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module UsageTests {
  method test0(x: int)
  {
    ghost var {:assumption} a0 := false;  // error
    ghost var a1, {:assumption} a2 := true, false;  // error
    ghost var {:assumption} a3: bool;
    ghost var {:assumption} a4;  // type of "a4" inferred to be bool

    a0 := a0 && (0 < x);

    a1 := a1 && true;

    a3 := true;  // error

    a3 := a2 && true;  // error

    a3 := a3 && true;
  }


  method test1()
  {
    ghost var {:assumption} a0: bool;

    a0 := true;  // error

    a0 := a0 && true;

    a0 := a0 && true;  // error
  }


  method test2()
  {
    ghost var {:assumption} a0: bool;

    a0 := a0 && true;

    if (false)
    {
      var a0 := 1;

      a0 := 2;

      a0 := 3;

      if (false)
      {
        ghost var {:assumption} a0: bool;

        a0 := a0;  // error

        if (false)
        {
          ghost var {:assumption} a0: bool;

          if (false)
          {
            ghost var {:assumption} a0 := false;  // error

            if (false)
            {
              ghost var {:assumption} a0: bool;

              a0 := a0 && true;

              a0 := a0 && true;  // error
            }
          }
        }
      }
    }
  }
}

module TypingTests {
  method test2()
  {
    ghost var {:assumption} a0: bool;

    a0 := a0 && true;

    if (false)
    {
      var a0 := 1;

      a0 := 2;

      a0 := 3;

      if (false)
      {
        ghost var {:assumption} a0: bool;

        a0 := a0;  // error

        if (false)
        {
          ghost var {:assumption} a0: bool;

          if (false)
          {
            ghost var {:assumption} a0 := 1;  // error: bad type
          }
        }
      }
    }
  }

  method test3() {
    ghost var {:assumption} a5: int;  // error: type must be bool
    var {:assumption} a: bool;  // error: assumption variable must be ghost
  }
}
