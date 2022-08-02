---
title: How do I pattern match against a head and tail of a sequence?
---

## Question

How do I pattern match against a head and tail of a sequence?
As in
```dafny
datatype Option<T> = None | Some(value:T)
var s: seq<int> := ...
var x := Option.Some(s);
match x  {
   case None => ...
   case Some(head, tail) => ...
}
```

## Answer

You can't. At least not like this. A `seq` in Dafny is like an array not like a data type of a list with a head and a tail.

You could use an if-case:
```dafny
if { 
  case x.None? => ...
  case x.Some? && .... predicate about x.value[0] and x.value[1...] ... => ...
}
