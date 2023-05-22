---
title: How do I model extern methods that return objects?
---

## Question: 

How do I model extern methods that return objects?


## Answer:

When modeling extern functions that return objects, it's usually not good to have specifications that return objects. 
It's better to have a predicate that takes the input of a function, an object, and relates the two to each other.

For example:

```dafny
trait {:extern} {:compile false} Test {
  var i: int
  var y: int
}
trait {:extern} {:compile false} Importer {
  function Import(i: int): (r: Test)
    ensures r.i == i

  method {:extern} {:compile false} DoImport(i: int) returns (r: Test)
    ensures r == Import(i)

  predicate Conditions(i: int) {
     && var r := Import(i);
     && r.y == 2
  }
}
```

In this case, it's better to write a predicate, and use existential quantifiers along with the `:|` operator, 
and there is no need to prove uniqueness because we are in ghost code!

```dafny
trait {:extern} {:compile false} Test {
  var i: int
}
trait {:extern} {:compile false} Importer {
  predicate IsImported(i: int, r: Test) {
    r.i == i
  }
  method {:extern} {:compile false} DoImport(i: int) returns (r: Test)
    ensures IsImported(i, r)

  predicate Conditions(i: int) {
     && (exists r: Test :: IsImported(i, r))
     && var r :| IsImported(i, r);   // Note the assignment has changed.
     && r.y == 2
  }
}
```
