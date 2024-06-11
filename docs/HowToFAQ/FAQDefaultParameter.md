---
title: How do I declare a default value for a parameter of a method or function?
---

## Question

How do I declare a default value for a parameter of a method or function?

## Answer

The parameters of methods and functions can be referred to by name.
```dafny
  method m( i: int,  j: int, k: int) {}
  method q() {
    m(4, k:= 7, j:=8);

  }
```
In the left-to-right sequence of actual arguments, once a parameter is referred to by name, all the rest must also be referred to by name. The named arguments may be in any order.

Furthermore, arguments can be given default values.
```dafny
  method m( i: int,  j: int, k: int := 0) {}
  method q() {
    m(4, 4, k:=8);
    m(1, j:=2);
    m(1,2);
  }
```
In the left-to-right sequence of actual arguments, once a parameter is given a default value, all the rest must also have a default value. Arguments may still be referred to by name, but now any named
argument with a default is optional. If there are no names at all, then it is always the last
arguments that are omitted if the actual argument list is shorter than the formal parameter list,
and they must all have defaults.

Finally, a parameter may be declared as `nameonly`, in which case it must be referred to by name.
```dafny
  method m( i: int,  j: int, nameonly k: int := 0, q: int := 8) {}
  method q() {
    // m(4, 4, 8 ); // Error
    m(4, 4, q:=9);
    m(4, 4, k:=8);
  }
```
Such a parameter may but does not need to have default value, but if it does not, it cannot be omitted.
