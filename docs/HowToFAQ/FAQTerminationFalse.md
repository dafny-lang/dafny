---
title: What do {:termination false} and @AssumeCrossModuleTermination do? It looks one of them is required if I want to extend traits from other modules.
---

## Question

What do `{:termination false}` and `@AssumeCrossModuleTermination` do? It looks one of them is required if I want to extend traits from other modules.

## Answer

These attributes allow a class to extend a trait from another module, even though termination checking may then miss cases of non-termination. Here is an example
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
In this example, omitting `{:termination false}` provokes the error "class 'Boz' is in a different module than trait 'foo1.Foo'. A class may only extend a trait in the same module, 
unless the class is annotated with `@AssumeCrossModuleTermination` or the parent trait is annotated with `{:termination false}`.".

These attributes are only needed when there is dynamic dispatch across module boundaries.
It does put the onus on the user to prove termiation, as Dafny may successfully verify the program even if some execution paths may never terminate.
The origin of this situation has to do with the interaction of current decreases clauses and traits.

Dafny decreases clauses were designed before the language had dynamic dispatch via trait members. As such, decreases clauses are made to be as simple as possible within each module, and decreases clauses are unnecessary across modules. When dynamic dispatch was added to the language, a draconian restriction was put in place to maintain soundness, namely to disallow dynamic dispatch across module boundaries. This is enforced by insisting that a class that implements a trait is declared in the same module that declares the trait.

The draconian restriction outlaws the useful case where a trait is placed in a library. 
The recommended approach is to NOT add `{:termination false}` to the trait,
but instead expect that any extending classes declared in other modules add `@AssumeCrossModuleTermination`.
This ensures that users of the library are made aware of this unsoundness and must opt-in to it.

The status of solutions to this problem are discussed [here](https://github.com/dafny-lang/dafny/issues/1588).
