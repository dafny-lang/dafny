---
title: Can datatypes extend traits?
---

## Question

I heard a rumor of datatypes extending traits coming in the pipeline. How will that work? Will we be able to use `is` and `as` with such types?

## Answer

Yes, datatypes can extend traits. To enable this functionality, you need to supply the command-line options
`--type-system-refresh --general-traits=datatype` (and, while you're at it, we suggest you also use `--general-newtypes`).
These options will become the default in Dafny 5.0.

Under these options, a trait is no longer necessarily a reference type. If you want to restrict a trait `MyTrait` to be a reference type,
declare it with `trait MyTrait extends object`.

The traits need to be declared when the datatype is declared; the trait cannot be added later on.

`is` and `as` are possible.
