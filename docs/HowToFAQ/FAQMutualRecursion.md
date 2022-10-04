---
title: How do I make Dafny termination checking happy with mutual recursion?
---

## Question

How do I make Dafny termination checking happy with mutual recursion, like the following example:
```dafny
datatype T = Y | N | B(T,T)

function f(x : T) : bool {
    match x {
        case Y => true
        case N => false
        case B(x,y) => g(x,y)
    }
}

function g(x : T, y : T) : bool {
    f(x) && f(y)
}
```

If `g` is inlined there is no problem. What should I do?

## Answer

Termination of recursion is proved using a `decreases` clause. For the single function
Dafny can successfully guess a decreases metric. But for this mutual recursion case,
the user must supply on.

The termination metric for a recursive datatype (like `T` here) is the height of the tree denoted by the argument `x`, in this case.
So there is definitely a decrease in the metric from the call of `f` to the call of `g`, but there is not when `g` calls `f`.
One solution to this situation is the following:
```dafny
datatype T = Y | N | B(T,T)

function f(x : T) : bool 
  decreases x, 1
{
    match x {
        case Y => true
        case N => false
        case B(x,y) => g(x,y)
    }
}

function g(x : T, y : T) : bool 
  decreases B(x,y), 0
{
    f(x) && f(y)
}
```
Here when `f` calls `g`, the metric goes from `x, 1` to `B(x.x, x.y), 0`. Because `x` is the same as `B(x.x, x.y)`, the lexicographic ordering looks
at the next component, which does decrease from `1` to `0`. Then in each case that `g` calls `f`, the metric goes from `B(x,y), 0` to `x,1` or `y,1`,
which decreases on the first component.

Another solution, which is a pattern applicable in other circumstances as well, is to use a ghost parameter as follows:
```dafny
datatype T = Y | N | B(T,T)

function method f(x : T) : bool
  decreases x, 1
{
  match x {
    case Y => true
    case N => false
    case B(x',y') => g(x,x',y')
  }
}

function method g(ghost parent: T, x : T, y : T) : bool
  decreases parent, 0
  requires x < parent && y < parent
{
  f(x) && f(y)
}
```

More on the topic of termination metrics can be found [here](../DafnyRef/DafnyRef#sec-decreases-clause).
