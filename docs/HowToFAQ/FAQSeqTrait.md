---
title: How can I combine sequences of different types?
---

## Question

How can I combine sequences of different types?

## Answer

It depends on the types. If the different types are subset types of a common base type, you can make a combined list of the base type. Similarly if the two types are classes (or traits) that extend a common trait, then you can combine sequences into a sequence of that trait. And since all classes extend the trait `object`, that can be the common type.

Here is some sample code:
```dafny
trait T {}
class A extends T {}
class B extends T {}

method m() {
  var a: A := new A;
  var sa: seq<A> := [ a ];
  var b := new B;
  var sb : seq<B> := [b ];
  var st : seq<T> := sa + sb;
  var so : seq<object> := sa + sb;
}
```

In fact, Dafny will generally infer a common type for you in the case of sequence concatentation.
