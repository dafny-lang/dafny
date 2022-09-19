---
title: I have a module that exports a bunch of things. In another module I only need to use 1 thing. Is there a way to import only the thing that I want?
---

## Question

I have a module that exports a bunch of things. In another module I only need to use 1 thing. Is there a way to import only the thing that I want?

## Answer

The short answer is: use an export set.

Here is an example. Suppose you have this code:
``` dafny
module A {
  export JustJ reveals j
  const i: int := 64
  const j: int := 128
}
module B {
  //import opened A // imports both i and j
  import opened A`JustJ // just imports j
}
```
The `export` directive in module `A` just exports the name `j` in the export set `JustJ`.
So then you can import just `j` in `B` by importing ``A`JustJ``.

You can create as many export sets as you like, for different contexts.
See the details [here](../DafnyRef/DafnyRef#sec-export-sets-and-access-control).

This feature does put the onus of defining the groups of exportable names on the supplying module.
Your question asks for such control by the receiving module. The best course for the receiving
module is to not use `import opened` and just use a qualified name for the one thing that is being used from the
supplying module.
