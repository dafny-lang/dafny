---
title: Can it be proved that a class instance is not an instance of a trait?
---

## Question

Can it be proved that a class instance is not an instance of a trait, as in the following example?
```dafny
trait A<T> {}

class B {}

lemma Foo(v: object)
  ensures v is B ==> !(v is A<object>)
{}
```

## Answer

No. Although the lemma is valid and may be stated as an axiom, Dafny does not internally model
the type hierarchy and so does not have the information to prove that statement.
Such an axiom would have to be manually checked against the type hierarchy if the definitions of 
the types involved were to change.
