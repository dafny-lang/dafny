---
title: A module A has names from an `import opened` of another module B, but if C imports A, it does not get those names. Please explain.
---

## Question

A module A has names from an `import opened` or another module B, but if C imports A, it does not get those names. Please explain.

## Answer

Here is some example code:
```dafny
module A {
  const a: int := 0
}

module B {
  import opened A
  const b: int := a; // This is A.a, known as a here because of the import opened
}

module C {
  import opened B
  const c: int := b; // This is B.b because of the import opened
  const d: int := A.a; // B.A is known as A because of the import opened in B
  const e: int := a; // ILLEGAL - opened is not transitive
}
```

The `import opened` directive brings into the importing module all the names declared in the imported module,
including the names of modules from import statements in the importee, but not names introduced into the importee (here `B`) by an import opened directive. `opened` is not transitive. As shown in the example code, the names in `A` are still available in `C` by qualifying them.
