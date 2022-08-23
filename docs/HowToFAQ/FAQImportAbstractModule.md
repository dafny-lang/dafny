---
title: Why can compiled modules contain but not import abstract modules?
---

## Question

Why can compiled modules contain but not import abstract modules?

## Answer

Keep in mind first that abstract modules are not compiled.

The enclosing module may declare an abstract module A and also a non-abstract module B that refines A.
A refining module import (`import D : C`) may only occur in an abstract module itself.

Generally speaking, suppose you have an underspecified module that is imported using ':', as in
```
abstract module Interface {
  function method addSome(n: nat): nat
    ensures addSome(n) > n
}
abstract module Mod {
  import A : Interface
  method m() {
    assert 6 <= A.addSome(5);
  }
}
```
Here `A` is abstract because it stands for any concrete module that adheres to the interface declared in `Interface`
(note that the function `addSome` has no body). Consequently `Mod` must be abstract as well.
`Interface` is not compilable, but it actually does not need to be declared `abstract`.

Now we can implement a concrete version of `Interface`:
```
module Implementation {
  function method addSome(n: nat): nat
    ensures addSome(n) == n + 1
  {
    n + 1
  }
}
```

Then we can implement the concrete module `Mod2` as a refinement of the abstract module `Mod`:
```
module Mod2 refines Mod {
  import A = Implementation
  ...
}
```
Here the module `Mod.A`, which is an unspecified refinement of `Interface` inside of `Mod`, is refined to be the concrete module
`Implementation` inside of `Mod2`, which is a refinement of `Mod`.

However, to the very specific point of the question:
```dafny
abstract module J {}

module K {
  abstract module JJ {}
  import J // ERROR
}
```
You are correct that abstract module `JJ` can be declared in `K`, but abstract module `J` cannot be imported.
This is somewhat of an anomaly in Dafny.
