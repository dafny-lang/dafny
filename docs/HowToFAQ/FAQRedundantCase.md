---
title: I just realized that a function I was compiling had a type error inside a match case.  Instead of giving a compile error I was getting a redundant clause warning for the second case. What is the reason for this?
---

## Question

I just realized that a function I was compiling had a type-error inside a match case.  Instead of giving a compile error I was getting a redundant clause warning for the second case. What is the reason for this?

## Answer

Here is a situation that can cause this error:
```dafny
datatype AB = A | B
method test(q: AB) {
  var c := match q { case a => true case b => false };
}
```
The example has an error on the second `case` saying this branch is redundant.

The problem here is that both `a` and `b` are undeclared variables. Consequently they both match
in match expression `q` no matter what `q`'s value is. Because `a` matches no matter what, 
the second case is redundant.

What is usually intended by such code is something like this:
```dafny
datatype AB = A | B
method test(q: AB) {
  var c := match q { case A => true case B => false };
}
```
which causes no type errors.

The observation here is that misspelled type names in case patterns can cause silent unexpected  behavior. It is likely that a lint warning will be produced for the above anti-pattern in some future version of Dafny.
