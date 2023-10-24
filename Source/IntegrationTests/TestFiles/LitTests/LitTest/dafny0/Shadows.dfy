// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --warn-shadowing


module Module0 {
  class C<alpha> {
    method M<beta, beta>(x: beta)  // error: duplicate type parameter
    method P<alpha>(x: alpha)  // shadowed type parameter
    ghost function F<beta, beta>(x: beta): int  // error: duplicate type parameter
    ghost function G<alpha>(x: alpha): int  // shadowed type parameter

    method Q0(x: int) returns (x: int)  // error: duplicate variable name
  }
}
module Module1 {
  class D {
    method Q1(x: int) returns (y: int)
    {
      var x;  // shadowed
      var y;  // error: duplicate
    }

    var f: int
    method R()
    {
      var f;  // okay
      var f;  // error: duplicate
    }
    method S()
    {
      var x;
      {
        var x;  // shadow
      }
    }
    method T()
    {
      var x;
      ghost var b := forall x :: x < 10;  // shadow
      ghost var c := forall y :: forall y :: y != y + 1;  // shadow
    }
  }
}

module Module2 {
  function
    {:myAttr var r := 10; r}
    {:warnShadowing false}
    {:myAttr
      var x := 2;
      var x := 3;
      x
    }
    F0(x: int): (r: int)
  {
    var x := 2;
    var x := 3;
    var r := 4;
    x
  }

  function
    {:myAttr var r := 10; r} // warning: r is shadowed
    {:warnShadowing true}
    {:myAttr
      var x := 2; // warning: x is shadowed
      var x := 3; // warning: x is shadowed
      x
    }
    F1(x: int): (r: int)
  {
    var x := 2; // warning: x is shadowed
    var x := 3; // warning: x is shadowed
    var r := 4; // okay
    x
  }

  function
    {:myAttr var r := 10; r} // warning: r is shadowed
    {:warnShadowing} // this is the same as {:warnShadowing true}
    {:myAttr
      var x := 2; // warning: x is shadowed
      var x := 3; // warning: x is shadowed
      x
    }
    F2(x: int): (r: int)
  {
    var x := 2; // warning: x is shadowed
    var x := 3; // warning: x is shadowed
    var r := 4; // okay
    x
  }

  function
    {:myAttr var r := 10; r} // warning: r is shadowed
    {:myAttr
      var x := 2; // warning: x is shadowed
      var x := 3; // warning: x is shadowed
      x
    }
    F3(x: int): (r: int)
  {
    var x := 2; // warning: x is shadowed
    var x := 3; // warning: x is shadowed
    var r := 4; // okay
    x
  }

  method
    {:myAttr var r := 10; r}
    {:warnShadowing false}
    {:myAttr
      var x := 2;
      var x := 3;
      x
    }
    M0(x: int) returns (r: int)
  {
    var x := 2;
    var x := 3; // error: duplicate variable
    var r := 4; // error: duplicate variable
  }

  method
    {:myAttr var r := 10; r} // warning: r is shadowed
    {:warnShadowing true}
    {:myAttr
      var x := 2; // warning: x is shadowed
      var x := 3; // warning: x is shadowed
      x
    }
    M1(x: int) returns (r: int)
  {
    var x := 2; // warning: x is shadowed
    var x := 3; // error: duplicate variable
    var r := 4; // error: duplicate variable
  }

  method
    {:myAttr var r := 10; r} // warning: r is shadowed
    {:warnShadowing} // this is the same as {:warnShadowing true}
    {:myAttr
      var x := 2; // warning: x is shadowed
      var x := 3; // warning: x is shadowed
      x
    }
    M2(x: int) returns (r: int)
  {
    var x := 2; // warning: x is shadowed
    var x := 3; // error: duplicate variable
    var r := 4; // error: duplicate variable
  }

  method
    {:myAttr var r := 10; r} // warning: r is shadowed
    {:myAttr
      var x := 2; // warning: x is shadowed
      var x := 3; // warning: x is shadowed
      x
    }
    M3(x: int) returns (r: int)
  {
    var x := 2; // warning: x is shadowed
    var x := 3; // warning: x is shadowed
    var r := 4; // warning: r is shadowed
  }
}
