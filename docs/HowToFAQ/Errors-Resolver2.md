
<!-- %check-resolve %default %useHeadings  -->

<!-- FILE ./DafnyCore/Resolver/TypeConstraint.cs-->

<!-- TODO: collector for other errors? -->

<!-- FILE ./DafnyCore/Resolver/TailRecursion.cs -->

## **Error: tail recursion can be specified only for methods that will be compiled, not for ghost methods**

```dafny
ghost method {:tailrecursion} m(n: nat) returns (r: nat)
{ 
  if n == 0 { r := 0; } else { r := m(n-1); }
}
```

Tail-recursion is a compilation optimization that transforms recursive calls into loops.
So it is only relevant to compiled code; ghost functions and methods need not
(and may not) specify a `{:tailrecursion}` attribute.

## **Error: sorry, tail-call optimizations are not supported for mutually recursive methods**

```dafny
method g(n: nat) returns (r: nat) { r := f(n); }
method {:tailrecursion} f(n: nat) returns (r: nat)
{ 
  if n == 0 { r := 0; } else { r := g(n-1); }
}
```

Tail-recursion is a compilation optimization that transforms recursive calls into loops.
However, the implementation currently in the `dafny` tool does not support identifying
and optimizing tail-recursion opportunities in mutually recursive functions.

## **Error: this recursive call is not recognized as being tail recursive, because it is followed by non-ghost code**

```dafny
method {:tailrecursion} m(n: nat) returns (r: nat)
{ 
  r := m(n-1);
  r := 0;
}
```

Tail-recursion is a compilation optimization that transforms recursive calls into loops.
As the name somewhat implies, a situation amenable to tail-recursion optimization 
is one in which the recursive call of the function or method is the last thing that
happens in the body of the function or method. If other code follows the recursive call,
the tail-recursion transformation cannot be applied.


## **Error: the recursive call to '_name_' is not tail recursive, because the assignment of the LHS happens after the call**

<!-- TODO -->

## **Error: a recursive call inside a loop is not recognized as being a tail call**

```dafny
method {:tailrecursion} m(n: nat) returns (r: nat)
{ 
  while n > 0 { r := m(n-1); }
}
```

Tail-recursion is a compilation optimization that transforms recursive calls into loops.
As the name somewhat implies, a situation amenable to tail-recursion optimization 
is one in which the recursive call of the function or method is the last thing that
happens in the body of the function or method. That is certainly not the case for calls
within loops, so such calls may not be attributed with `{:tailrecursion}`.

<!-- 2 instances -->

## **Error: a recursive call inside a forall statement is not a tail call**

<!-- TODO -->

## **Error: a recursive call in this context is not recognized as a tail call**

<!-- TODO -->

## **Error: the recursive call to '_name_' is not tail recursive because the actual out-parameter is not the formal out-parameter _formal_**

```dafny
method {:tailrecursion} m(n: nat) returns (r: nat)
{ 
  var x := m(n-1);
}
```

Tail-recursion is a compilation optimization that transforms recursive calls into loops.
Part of the pattern that is amenable to this optimization is that the last thing happening 
in the body of a recursive method (or function) is a call of the recursive function with the
value returned being assigned to the out-parameter.

## **Error: the recursive call to '_name_' is not tail recursive because the actual out-parameter _out_ is not the formal out-parameter _formal_**

```dafny
method {:tailrecursion} m(n: nat) returns (r: nat, s: nat)
{ 
  var x, y := m(n-1);
}
```

Tail-recursion is a compilation optimization that transforms recursive calls into loops.
Part of the pattern that is amenable to this optimization is that the last thing happening 
in the body of a recursive method (or function) is a call of the recursive function with the
value returned being assigned to the out-parameter.

## **Error: the recursive call to '_name_' is not tail recursive because the actual type argument _typeparam_ is not the formal type parameter '_formal_'**

```dafny
method {:tailrecursion} m<T,U>(n: nat) returns (r: nat)
{ 
  if n == 0 { return 0; } else { r := m<U,U>(n-1); }
}
```

If the method that is marked for tail-recursion has type parameters, then the recursive 
calls of that method must have the same type parameters, in the same order.
Note that type parameter positions start from 0.


## **Error: tail recursion can be specified only for functions that will be compiled, not for ghost functions**

<!-- %check-resolve %options --function-syntax:4 -->
```dafny
ghost function {:tailrecursion} f(n: nat): int
{ 
  if n == 0 then 0 else f(n-1)
}
```

Tail-recursion is a compilation optimization that transforms recursive calls into loops.
So it is only relevant to compiled code; ghost functions and methods need not
(and may not) specify a `{:tailrecursion}` attribute.

## **Error: sorry, tail-call optimizations are not supported for mutually recursive functions**

<!-- %check-resolve %options --function-syntax:4 -->
```dafny
function g(n: nat): nat { f(n) }
function {:tailrecursion} f(n: nat): nat
{ 
  if n == 0 then 0 else g(n-1)
}
```

Tail-recursion is a compilation optimization that transforms recursive calls into loops.
However, the implementation currently in the `dafny` tool does not support identifying
and optimizing tail-recursion opportunities in mutually recursive functions.

## **Error: if-then-else branches have different accumulator needs for tail recursion**

<!-- TODO -->

## **Error: cases have different accumulator needs for tail recursion**

<!-- TODO -->

<!-- 2 instances -->


## **Error: to be tail recursive, every use of this function must be part of a tail call or a simple accumulating tail call**

<!-- %check-resolve %options --function-syntax:4 -->
```dafny
function {:tailrecursion} f(n: nat): nat
{
  if n == 0 then n else var r := f(n-1); r
}
```

<!-- %check-resolve %options --function-syntax:4 -->
```dafny
function {:tailrecursion} f(n: nat): nat
{
  if n < 2 then n else f(n-2)+f(n-1)
}
```

Tail-recursion is a compilation optimization that transforms recursive calls into loops.
The Dafny compiler analyzes the code for recognizable, not too complex patterns.
One complexity that defies analysis is too many calls of the same recursive function;
another is using the function as a value, rather than in a function call.


<!-- FILE ./DafnyCore/Resolver/Resolver.cs -->

<!-- TODO Lots -->

