---
title: I have a lemma and later an assert stating the postcondition of the lemma, but it fails to prove. Why and how do I fix it?
---

## Question: I have a lemma and later an assert stating the postcondition of the lemma, but it fails to prove. Why and how do I fix it?

I have this lemma
```dafny
    lemma MapKeepsCount<X,Y,Z>(m : map<X,Y>, f : (X) -> Z)
      requires forall a : X, b : X :: a != b ==> f(a) != f(b)
      ensures |m| == |map k <- m.Keys | true :: f(k) := m[k]|
```
and later on this code
```dafny
MapKeepsCount(authSchema, k => Paths.SimpleCanon(tableName, k));
assert |authSchema| == |map k <- authSchema.Keys | true :: Paths.SimpleCanon(tableName, k) := authSchema[k]|;
```

The final assert fails, even though it exactly matches the ensures of the lemma.
What am I missing? 

If the lemma is an axiom, one can try to assume the post condition right before the assertion. 
But that failed in this case

```dafny
MapKeepsCount(authSchema, k => Paths.SimpleCanon(tableName, k));
assume |authSchema| == |map k <- authSchema.Keys | true :: Paths.SimpleCanon(tableName, k) := authSchema[k]|;
assert |authSchema| == |map k <- authSchema.Keys | true :: Paths.SimpleCanon(tableName, k) := authSchema[k]|;
```

Which makes no sense.
I even put the function into a variable, and this still fails
```dafny
assume |authSchema| == |map k <- authSchema.Keys :: fn(k) := authSchema[k]|;
assert |authSchema| == |map k <- authSchema.Keys :: fn(k) := authSchema[k]|;
```

## Answer:

The explanation is a little involved, and in the end gets into a weakness of Dafny. But I also have a workaround. Get some popcorn. Here goes:

To prove that the `|map …|` expression in the specification has the same value as the `|map …|` expression in the code, 
the verifier would either have to compute the cardinality of each map (which it can’t do, because m.Keys is symbolic and could stand for any size set) 
or reason that the one map … is the very same map as the other map … (in which case it would follow that the cardinality of the two maps are also the same).
The way to prove that two maps are equal is to show that they have the same keys and the same mappings. 
The idea of proving two things equal by looking at the “elements” of each of the two things is called extensionality. 
Dafny never tries to prove extensionality, but it’s happy to do it if you ask it to. 
For example, if G is a function that you know nothing about and you ask to prove
```dafny
assert G(s + {x}) == G({x} + s + {x});
```
then Dafny will complain. You have to first establish that the arguments to these two invocations of `G` are the same, which you can do with an assert:
```dafny
assert s + {x} == {x} + s + {x};
assert G(s + {x}) == G({x} + s + {x});
```

Here, Dafny will prove the first assertion (which it actually does by proving that the sets are elementwise equal) and will then use the first assertion to prove the second.
Going back to your example, Dafny needs to know that the two `map`s are equal. To help it along, perhaps you could mention the two in an assertion, like

`assert map … == map …;`

But you can’t do that here, because the two map expressions are in different scopes and use different variables.
To establish that the two maps are equal, we thus need to do something else. 
If the two of them looked the same, then Dafny would know that the are the same. 
But the form is slightly different, because you are (probably without thinking about it) instantiating a lambda expression. 
To make them the same, you could rewrite the code to:
```dafny
  var F := k => Paths.SimpleCanon(tableName, k);
  MapKeepsCount(authSchema, F);
  assert |authSchema| == |map k <- authSchema.Keys | true :: F(k) := authSchema[k]|;
```

Now, this `map …` syntactically looks just like the one in the lemma postcondition, but with authSchema instead of m and with F instead of f. 
When two map comprehensions (or set comprehensions, or lambda expressions) are syntactically the same like this, then Dafny knows to treat them the same.
Almost. 
Alas, there’s something about this example that makes what I said not quite true (and I didn’t dive into those details just now). 
There is a workaround, and this workaround is often useful in places like this, so I’ll mention it here. 
The workaround is to give the comprehension a name. Then, if you use the same name in both the caller and callee, 
Dafny will know that they are the same way of constructing the map. 
The following code shows how to do it: 
```dafny
lemma MapKeepsCount<X, Y, Z>(m: map<X, Y>, f: X -> Z)
  requires forall a : X, b : X :: a != b ==> f(a) != f(b)
  ensures |m| == |MyMap(f, m)|

function MyMap<X, Y, Z>(f: X -> Y, m: map<X, Z>): map<Y, Z>
  // (you can use the <- syntax in the following lines, by the Dafny Playground uses
  // an older version of Dafny that didn't yet support that syntax)
  requires forall a, b | a in m.Keys && b in m.Keys :: a != b ==> f(a) != f(b)
{
  // same comment about <- in the next line
  map k | k in m.Keys :: f(k) := m[k]
}

method Use<X,Y,Z>(authSchema: map<X,Y>, tableName: Paths.TableName)
  requires forall a : X, b : X :: a != b ==> Paths.SimpleCanon(tableName, a) != Paths.SimpleCanon(tableName, b)
{
  var F := k => Paths.SimpleCanon(tableName, k);
  MapKeepsCount(authSchema, F);
  assert |authSchema| == |MyMap(F, authSchema)|;
}

module Paths {
  type TableName

  function method SimpleCanon<K>(t: TableName, k: K): int
}
```

It manually introduces a function MyMap, and by using it in both caller and callee, the code verifies.

Being “injective” is the mathematical description of any function f that satisfies the property you’re giving in the precondition. 
Another name for “injective” is “one-to-one” (which sounds more symmetric than it is--hence, the name “injective” is probably better).