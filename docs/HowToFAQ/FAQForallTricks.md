---
title: Why can't I write 'forall t: Test :: t.i == 1' for an object t?
---

## Question:

Why can't I write `forall t: Test :: t.i == 1` for an object t?

## Answer:

This code

```dafny
trait Test {
 var i: int
}
class A {
  predicate testHelper() {
    forall t: Test :: t.i == 1
    // a forall expression involved in a predicate definition is not allowed to depend on the set of allocated references,
  }
}
```

can be better written as

```dafny
trait Test {
 var i: int
}
class A {
  ghost const allTests: set<Test>
  predicate testHelper() reads allTests {
    forall t: Test <- allTests :: t.i == 1
  }
}
```

That way, if you want to assume anything about the Test classes that you are modeling extern, 
you only need to specify an axiom that says that whatever Test you have was in allTests, 
which could have been a pool of Test objects created from the start anyway, and then you can use your axiom. 