// RUN: %baredafny translate cs %args --compile-target "%s" %S/ExternDLL2.cs %S/ExternHelloLibrary.dll > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  Mod1.Test();
  ConstInit.Test();
  TwoArgumentExtern.Test();
}

module {:extern "Modx"} Mod1
{
  class {:extern "classx"} Class1
  {
    static function method {:extern "Fun1x"} Fun1() : int
      ensures Fun1() > 0
    static method {:extern "Method1x"} Method1() returns (x: int)
      ensures x > 0
    static function method Fun2() : int
      ensures Fun2() > 0
    {
      Fun1()
    }
    static method Method2() returns (x: int)
      ensures x > 0
    {
      x := Method1();
    }
  }
  method Test()
  {
    var m2 := Class1.Method2();
    print "Fun2() = ", Class1.Fun2(), ", Method2() = ", m2, "\n";
  }
}

module {:extern "ConstInit"} ConstInit {
  class C { }

  const {:extern} c: C  // because it's extern, it's okay not to have a defining value

  class W {
    static const {:extern} f: C  // because it's extern, it's okay not to have a defining value
  }

  class U {
    // the initial/defining values of d and e must be provided by the extern constructor
    var d: C
    const e: C
    constructor {:extern} (b: bool)
  }

  method Test() {
    Check(c);
    Check(W.f);

    var u := new U(true);
    Check(u.d);
    Check(u.e);
  }

  method Check(o: object?)
    requires o != null
  {
    print if o == null then "null" else "good", "\n";
  }
}

module TwoArgumentExtern {
  method {:extern "ABC.DEF", "MX"} M(x: int) returns (r: int)

  // git issue 423
  function method {:extern "ABC.DEF", "FX"} F(x: int): int

  method Test() {
    var y := M(2);  // calls ABC.DEF.MX
    var z := F(2);  // calls ABC.DEF.FX
    print y, " ", z, "\n";  // 4 2
  }
}
