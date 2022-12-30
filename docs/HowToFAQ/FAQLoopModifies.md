---
title: If I have an assertion about an object (of class type) and a loop that doesn't mention (read, modify) the object, why does dafny fail to establish the assertion after the loop?
---

## Question

If I have an assertion about a class and a loop that doesn't mention (read, modify) the class, 
why does dafny fail to establish the assertion after the loop?

## Answer

The short answer is that you need an appropriate combination of modifies clauses and 
loop invariants to prove assertions about the end result of a loop.

In Dafny's way of reasoning about a loop (which is typical of verifier systems), 
the loop invariant is the only thing you can assume at the top of every iteration. 
In other words, at the top of each loop iteration, it is as if all variables have 
arbitrary values, with the condition that the loop invariant is satisfied. 
Sometimes, the word _havoc_ is used to describe this: the verifier havocs all variables, 
that is, gives all variables arbitrary values, and then assumes the loop invariant.

If that’s all the verifier did, life would be a pain, because you’d have to write a
loop invariant about all variables in your program, even those that have nothing to do with the loop.
The verifier actually does better. Instead of havocing all variables, it suffices to havoc 
the assignment targets within the body of the loop, including anything that might be modified by methods called in the loop body. 
That is, the verifier uses a simple syntactic scan of the loop body to see which 
variables may possibly be assigned, and then it havocs only those variables. 
This saves users from having to write loop invariants about all other variables.
Only invariants about variables that are modified are needed.

What about the heap? For this purpose, the heap is considered to be one variable. 
So, the heap is either an assignment target of the loop or it isn’t. 
This means that if your loop body assigns to anything in the heap, the heap becomes an assignment target. 
Also, if the loop body allocates another object, that too is a change of the heap, 
so the heap becomes an assignment target. 
Furthermore, Dafny’s rule about a method is that a method is allowed to change the 
state of any object in the method’s modifies clause, 
and it is also allowed to allocate new objects and to modify their state. 
Therefore, if your loop body calls a method, then the heap may well become an assignment target.

So, then, does this mean your loop invariant needs to speak about everything in the heap whenever the heap is an assignment target of the loop?

Again, no. Loops in Dafny have `modifies` clauses, just like methods do (and just like for methods, 
newly allocated objects are implicitly included in those `modifies` clauses). 
It would be a pain to even have to write `modifies` clauses for every loop, 
so if a loop does not have an explicit `modifies` clause, Dafny implicitly attaches 
the `modifies` clause of the enclosing method (or of the enclosing loop, in the case of nested loops). 
This default behavior turns out to be right in almost all cases in practice, 
which is why you normally don’t have to think about this issue.

But when it is not, you need to be explicit about the `modifies` clause and the loop invariants. 
In particular
- write a `modifies` clause for the loop that includes all objects whose fields might be 
assigned in the loop body (or listed in the modifies clauses of anything the loop body calls)
- then write a loop invariant that includes assertions about any variable that is listed in the modifies clause
or is an assignment target in the loop body. 
Very typically, the invariant will give a value for ecah havoced variable showing its relationship to the loop index.

For example, a loop that sets the elements of an array to some initial value might look like this:
```dafny
method init(a: array<int>) 
  modifies a
  ensures forall j | 0 <= j < a.Length :: a[j] == j
{
  var i := 0;

  while i < a.Length
    modifies a
    invariant 0 <= i <= a.Length && forall j | 0 <= j < i :: a[j] == j
  {
    a[i] := i;
    i := i + 1;
  }
}
```

Note the following points:
- The method specifies that it might modify the elements of the array `a`.
- The loop says that it modifies the same array. 
In fact that modifies clause could be omitted
because it would be inherited from the enclosing context.
- The loop also modifies `i`, but as `i` is a local variable, it need not be listed in the modifies clause.
- The loop also has an invariant, which has two conjuncts:
   - One conjunct states about the local variable `i`. Even though `i` is not in the modifies clause 
    it is an assignment target, so we need to say what is known about it (prior to the loop test).
   - The other conjunct talks about the elements of `a`, which depend on `i`, 
    that is, on how many iterations of the loop have been executed.
- After the loop, Dafny uses the loop invariant and the negation of the loop guard to conclude i == a.Length, and from that and the invariant, Dafny can prove the method's postcondition.

Even when Dafny can infer an appropriate modifies clause, it does not infer loop invariants, so the user always needs to supply those. 

Here is another example:
```dafny
class Counter {
  var n: nat
}

// print "hello" c.n times and then increment c.n
method PrintAndIncrement(c: Counter)
  modifies c
  ensures c.n == old(c.n) + 1
{
  for _ := 0 to c.n
    // To verify this method, the loop needs one of the following two lines:
    invariant c.n == old(c.n)
    modifies {} // empty modifies clause
  {
    PrintHello();
  }
  c.n := c.n + 1;
}

method PrintHello() {
  print "hello\n";
}
```
The inner for-loop can be specified and the whole method verified in two different ways.

First, suppose we do not include a modifies clause in the loop specifications of the inner loop.
Then dafny will use the enclosing modifies clause, which allows changing the
state of `c`. In order for the outer loop to know that the inner loop has not 
changed `c.n`, the inner loop needs the invariant `c.n == old(c.n)`.

Alternatively, the inner loop can specify its own modifies clause,
`modifies {}`, saying it modifies nothing. Then it follows directly that
`c.n` does not change in the inner loop, so no invariant is needed to carry out the proof.
