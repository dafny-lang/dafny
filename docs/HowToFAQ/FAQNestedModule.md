---
title: Can I access the members of an outer module from its inner module?
---

## Question

Can I access the members of an outer module from its inner module?
```dafny
{% include_relative FAQNestedModule.dfy %}
```

## Answer

No. The above example gives the error messages
```text
{% include_relative FAQNestedModule.txt %}
```

From a module you may access your own nested modules.
You may also access sibling modules and nested modules of sibling modules, but you need to import them.
That includes sibling modules of a module's own enclosing modules.
You may not access members of enclosing modules, including members declared at the global level (which are members of an implicit top-level module that includes everything in the program).

In general, there is a dependency order among modules: a module _depends on_ modules whose members it uses.
A module depends on its own nested modules.
A program cannot have circular dependencies: a module A cannot use members of module B if B (transitively) depends on A.

```dafny
module A {
  module B {
    const S1 := 10
  }
}

const S2 := 21
const S3 := C.D.A.B.S1 // OK

module C {
  module D {
    import A // OK - A is sibling of C
    import A.B // OK
    import E // OK - E is sibling of D
    import E.F // OK
    // import C // NOT OK - C is enclosing module
    // import EE = C.E // NOT OK -- can't access enclosing module
    // const X := S2 // NOT OK -- can't access top-level module
    const Y := B.S1 // OK - B is imported module
  }
  module E {
    module F {
    }
  }
}
```

