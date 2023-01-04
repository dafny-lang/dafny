---
title: A `seq` is an object reference, right?
---

## Question

A `seq` is an object reference, right?

## Answer

No. Types in Dafny are either heap-dependent (reference) types or strict value-types. Built-in types are typically value types.
Value types are heap independent, though they may be stored in the heap as part of an object.

Value types include `bool`, `int`, `char`, `real`, `ORDINAL`, datatypes and co-datatypes, arrow types, bit-vector types, `seq`, `set`, `iset`, `multiset`, `map`, `imap`, `string`, tuple types,  and subset or newtypes with value type bases.

Reference types are classes, traits, arrays, and iterators.

The values of value types are immutable; new values may be computed but are not modified. Integers are a good mental
model for value types, but in Dafny, datatypes, sequences, sets, and maps are also immutable values. 
Note that though the values of these types are immutable,
they may contain instances of reference types (which might be mutable).
