// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module AbstractModuleA 
{
  type T
} 

abstract module AbstractModuleB 
{
  import opened AMA : AbstractModuleA

  method Foo(t:T)
} 

abstract module AbstractModuleC refines AbstractModuleB 
{
  import opened AMA2 : AbstractModuleA
}

module LibA {
  class G { 
    static function f(x:int) : bool {
      x >= 10
    }
  }

  function g() : bool {
     true
  }
}

module LibB {
  class G { 
    static function f(x:int) : bool {
      x < 10
    }
  }

  function g() : bool {
     false
  }
}

module R {
  import opened LibA
}

module S refines R {
  import opened LibB
  method m() {
    assert g();  // should be LibA.g
  }

  method m1() {
   assert G.f(20); // should be LibA.G.f
  }
} 
