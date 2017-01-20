// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate isEven(x:int) 
{
  x % 2 == 0
}

function f(x:int, y:int): (z:int)
  requires x>0 && y > 0
  ensures z >= 10
	ensures f(x,y) == z
  ensures isEven(z)
{
	  2*(x+y) + 10
}

twostate function P2(x: int) : (z: int)
  ensures z == x - 1
	ensures P2(x) == z
	ensures P2(x) == x - 1
{
   x - 1
}

module Interface 
{
  function addSome(n: nat): nat
    ensures addSome(n) > n
}

module Implementation refines Interface 
{
  function addSome(n: nat): (z: nat)
    ensures z == n + 1
  {
    n + 1
  }
}

function foo(x:int, y:int) : (v: (int, int))
  ensures v == (x, y)
{
  (x, y)
}