---
title: Why can compiled modules contain but not import abstract modules?
---

## Question

Why can compiled modules contain but not import abstract modules?

## Answer

The question refers to code like this:
```dafny
abstract module J {}

module K {
  abstract module JJ {}
  import J // ERROR
}
```
It is indeed the case that the abstract module `JJ` can be declared in non-abstract module `K` but the abstract module `J` is not permitted to be imported.
This discrepancy is the subject of a proposed change to Dafny rules (cf. [issue #2635](https://github.com/dafny-lang/dafny/issues/2635)).

In either cases, however, there are limits on what can be done with an abstract submodule.
It is first of all not compiled as part of the enclosing module. Thus it can only be used as the subject of refinement.

That feature is described in the remainder of this FAQ.

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