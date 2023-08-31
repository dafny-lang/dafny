// RUN: %dafny /compile:0 /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate isEven(x:int)
{
  x % 2 == 0
}

ghost function f(x:int, y:int): (z:int)
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
  ghost function addSome(n: nat): nat
    ensures addSome(n) > n
}

module Implementation refines Interface
{
  ghost function addSome(n: nat): (z: nat)
    ensures z == n + 1
  {
    n + 1
  }
}

ghost function foo(x:int, y:int) : (v: (int, int))
  ensures v == (x, y)
{
  (x, y)
}

// bar will not be marked as recursive
ghost function bar(x:int, y:int) : int
 ensures bar(x, y) == 10
{
   10
}

// bar1 will be marked as recursive
ghost function bar1(x:int, y:int) : int
 ensures bar1(x, y+0) == 10
{
   10
}

// bar2 will be marked as recursive
ghost function bar2(x:int, y:int) : int
  ensures bar2((x), y) == 10
{
  10
}

