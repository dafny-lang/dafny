// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
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
}
// Will give error about duplicate CompileName for module.
extern "Modx" module Mod2
{
}
