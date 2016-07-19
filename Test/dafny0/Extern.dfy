// RUN: %dafny /compile:1 /print:"%t.print" /dprint:"%t.dprint" "%s" "%S\Extern2.cs" "%S\ExternHelloLibrary.dll" > "%t"
// RUN: %diff "%s.expect" "%t"
extern "Modx" module Mod1 
{
  extern "classx" class Class1
  {
    extern "Fun1x" static function method Fun1() : int
      ensures Fun1() > 0
    extern "Method1x" static method Method1() returns (x: int)
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
  method Main()
  {
    var m2 := Class1.Method2();
    print ("Fun2() = ", Class1.Fun2(), "Method2() = ", m2, "\n");
  }
}
