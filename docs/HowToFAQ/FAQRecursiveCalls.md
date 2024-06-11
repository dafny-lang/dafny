---
title: Are there functional alternatives to recursive calls that are more efficient or use less stack space?
---

## Question

Are there functional alternatives to recursive calls that are more efficient or use less stack space?

## Answer

One way to reduce the number of recursive calls is to use Dafny's function-by-method construct to give a better performing implementation.
For example
```dafny
function Fib(n: nat): nat {
  if n < 2 then n else Fib(n-1) + Fib(n-2)
}
```
it a very natural but quite inefficient implementation of the Fibonacci function (it takes `Fib(n)` calls of `Fib` to compute `Fib(n)`, though only to a stack depth of `n`).

With function-by-method we can still use the natural recursive expression as the definition but provide a better performing implementation:
```dafny
function Fib(n: nat): nat
 {
  if n < 2 then n else Fib(n-1) + Fib(n-2)
} by method {
  var x := 0;
  var y := 1;
  for i := 0 to n 
    invariant x == Fib(i) && y == Fib(i+1)
  {
    x, y := y, x+y;
  }
  return x;
}
```
This implementation both combines the two computations of Fib and also, more importantly, turns a tail recursive recursion into a loop.
