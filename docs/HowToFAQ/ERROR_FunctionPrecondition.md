---
title: "Error: possible violation of function precondition for op(v)"
---

Here is code that provoked this error (though the error message as been made more specific in later releases):
```dafny
function Eval(): string -> bool {
   EvalOperator(Dummy)
}

function EvalOperator(op: string -> bool): string -> bool 
{
  (v: string) => op(v)
}

function method Dummy(str: string): bool
  requires str == []
```

The problem has to do with [arrow types](../../DafnyRef/DafnyRef#sec-arrow-types).
In particular here, the argument of `EvalOperator` takes a `->` function, which is a total, heap-independent function.
However, its argument, `Dummy`, is a partial, heap-independent function, because it has a precondition.
If you want `EvalOperator` to be flexible enough to take partial functions, then declare `op` to have the type
`string --> bool`.

There is more on arrow types in the [reference manual](../DafnyRef/DafnyRef.html#sec-arrow-subset-types);
