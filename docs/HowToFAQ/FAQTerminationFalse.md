---
title: What does {:termination false} do on trait? It looks like it is required if I want to extend traits from other modules.
---

## Question

What does `{:termination false}` do on trait? It looks like it is required if I want to extend traits from other modules.

## Answer

The attribute turns off termination checking for the trait. Here is an example
```dafny
module foo1 {

  trait {:termination false} Foo {
    method bar()
  }

  class Baz{

    static method boz(foo: Foo){ foo.bar(); }

  }
}
module foo2 {

  import opened foo1

  class Boz extends Foo {

    method bar(){
      Baz.boz(this);
    }
  }
}
```
In this example, omitting `{:termination false}` provokes the error "class 'Boz' is in a different module than trait 'foo1.Foo'. A class may only extend a trait in the same module, unless the parent trait is annotated with {:termination false}.".

The `{:termination false}` is only needed when there is dynamic dispatch across module boundaries.
It does put the onus on the user to prove termiation, as Dafny is no longer doing so.
The origin of this situation has to do with the interaction of current decreases clauses and traits.

Dafny decreases clauses were designed before the language had dynamic dispatch via trait members. As such, decreases clauses are made to be as simple as possible within each module, and decreases clauses are unnecessary across modules. When dynamic dispatch was added to the language, a draconian restriction was put in place to maintain soundness, namely to disallow dynamic dispatch across module boundaries. This is enforced by insisting that a class that implements a trait is declared in the same module that declares the trait.

The draconian restriction outlaws the useful case where a trait is placed in a library. Indeed, we are seeing this in [`dafny-lang/libraries`](https://github.com/dafny-lang/libraries/) now. So, Dafny supports a way for users to lift the draconian restriction and instead take responsibility themselves for termination of dynamically dispatched calls via a trait--it is to mark the trait with `{:termination false}`.

The status of solutions to this problem are discussed [here](https://github.com/dafny-lang/dafny/issues/1588).
