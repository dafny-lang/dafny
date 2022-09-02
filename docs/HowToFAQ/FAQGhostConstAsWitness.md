---
title: Why can a ghost const not be used as a witness? Does the compiler need to use the witness as an initial value?
---

## Question

Why can a ghost const not be used as a witness? Does the compiler need to use the witness as an initial value?

## Answer

A type can be
- auto-initializing (which means the compiler knows of a value of the type)
- nonempty (which means there is a value of the type, but the compiler might not know it)
- possibly empty (neither or the above is true)

To show a type is auto-initializing, you may need to provide a witness clause. The expression given in the witness clause must be compilable.
To just show a type is nonempty, you can use a ghost witness clause. It takes a ghost expression, so you should be able to use your ghost const here.
If you don’t care about either, you can say `witness *`, which makes the type be treated as possibly empty.

When declaring generic types, one can use _type characteristics_ to indicate any restrictions on the types that may be substituted for a type parameter.
For example, writing `class A<T(0)>` says that types substituted fo `T` must be auto-initializing;
writing `class A<T(00)>` says that such types must be non-empty.
