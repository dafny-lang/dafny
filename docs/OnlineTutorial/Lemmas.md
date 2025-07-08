---
title: Lemmas and Induction
---

# Lemmas and Induction

## Introduction

Sometimes there are steps of logic required to prove a program correct,
but they are too complex for Dafny to discover and use on its own. When
this happens, we can often give Dafny assistance by providing a *lemma*.

Lemmas are theorems used to prove another result, rather than being a
goal in and of themselves. They allow Dafny to break the proof into two:
prove the lemma, then use it to prove the final result; the final result
being the correctness of the program. By splitting it in this way, you
can prevent Dafny from trying to bite off more than it can chew. Dafny,
like computers in general, is very good at dealing with a bunch of specific
details and covering all the cases, but it lacks the cleverness to see
intermediate steps that make the proof process easier.

By writing and using lemmas, you can point out what these steps are
and when to use them in a program. They are particularly important for
inductive arguments, which are some of the hardest problems for theorem
provers.

## Searching for Zero

As our first look at lemmas, we will consider a somewhat contrived example: searching
for zero in an array. What makes this problem interesting is that the array we are
searching in has two special properties: all elements are non-negative, and each successive
element decreases by at most one from the previous element. In code:

<!-- %check-verify Lemmas.1.expect %options -->
```dafny
method FindZero(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
{
}
```

With these requirements, we can do something clever in our search routine: we can skip
elements. Imagine that we are traversing through the array, and we see `a[j] == 7`.
Then we know that `6 <= a[j+1]`, `5 <= a[j+2]`, etc. In fact, the next zero can't
be until 7 more elements in the array. So we don't even have to search for a zero until
`a[j+a[j]]`. So we could write a loop like:

<!-- %check-verify Lemmas.2.expect -->
```dafny
method FindZero(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
{
  index := 0;
  while index < a.Length
    invariant 0 <= index
    invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0
  {
    if a[index] == 0 { return; }
    index := index + a[index];
  }
  index := -1;
}
```

This code will compute the right result, but Dafny complains about the second loop invariant.
Dafny is not convinced that skipping all those elements is justified. The reason is that the
precondition says that each successive element decreases by at most one, but it does not say
anything about how elements further away are related. To convince it of this fact, we need to
use a *lemma*.

## Lemmas

A `lemma` is syntactially a ghost method: the desired property stated by the lemma (more
precisely, the conclusion of the lemma) is declared as the postcondition, just like you
would for an ordinary method.  Unlike a method, a lemma is never allowed to change the
state.  Since a lemma is ghost, it doesn't need to be called at run time, so the compiler
erases it before producing executable code. The lemma is present solely for its effect
on the verification of the
program. You may think of lemmas as heavyweight assertions, in that they are only
necessary to help the proof of the program along. A typical lemma might look like:

<!-- %no-check -->
```dafny
lemma Lemma(...)
  ensures (desirable property)
{
  ...
}
```

For the zero search problem, the desirable property is that none of the elements from
`index` until `index + a[index]` can be zero. We take the array and the index
to start from as parameters, with the usual requirements from `FindZero`:

<!-- %check-verify Lemmas.3.expect -->
```dafny
lemma SkippingLemma(a: array<int>, j: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  requires 0 <= j < a.Length
  ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0
{
  //...
}
```

The postcondition is just the desirable property that we want. The extra restriction
on `i` is because `j + a[j]` could be past the end of the array. We only
want to talk about indices in that range which are also indices into the array. We
then do a crucial step: check that our lemma is sufficient to prove the loop invariant.
By making this check before filling in the lemma body, we ensure that we are trying to
prove the right thing. The `FindZero` method becomes:

<!-- %check-verify Lemmas.4.expect  -->
```dafny
lemma SkippingLemma(a: array<int>, j: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  requires 0 <= j < a.Length
  ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0
{
  //...
}
method FindZero(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
{
  index := 0;
  while index < a.Length
    invariant 0 <= index
    invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0
  {
    if a[index] == 0 { return; }
    SkippingLemma(a, index);
    index := index + a[index];
  }
  index := -1;
}
```

Now Dafny does not complain about the `FindZero` method, as the
lemma's postcondition shows that the loop invariant is preserved. It does
complain about the lemma itself, which is not surprising given that the
body is empty. In order to get Dafny to accept the lemma, we will have to
demonstrate that the postcondition is true. We do this like we do everything
in Dafny: writing code.

We start with the crucial property of the array, that it only decreases
slowly. We can ask whether certain properties hold by using assertions. For
example, we can see that Dafny knows:

<!-- %check-verify -->
```dafny
lemma SkippingLemma(a: array<int>, j: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  requires 0 <= j < a.Length - 3
  // Note: the above has been changed so that the array indices below are good.
{
  assert a[j  ] - 1 <= a[j+1];
  assert a[j+1] - 1 <= a[j+2];
  assert a[j+2] - 1 <= a[j+3];
  // therefore:
  assert a[j  ] - 3 <= a[j+3];
}
```

Thus we can see that Dafny can follow along in any individual step, and can
even chain them appropriately. But the number of steps we need to make is not
constant: it can depend on the value of `a[j]`. But we already have a
construct for dealing with a variable number of steps: the while loop!

We can use the very same construct here to get Dafny to chain the steps
together. We want to iterate from `j` to `j + a[j]`, keeping
track of the lower bound as we go. We also keep track of the fact that all
of the elements we have seen so far are not zero:

<!-- %check-verify -->
```dafny
lemma SkippingLemma(a: array<int>, j: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  requires 0 <= j < a.Length
  ensures forall k :: j <= k < j + a[j] && k < a.Length ==> a[k] != 0
{
  var i := j;
  while i < j + a[j] && i < a.Length
    invariant i < a.Length ==> a[j] - (i-j) <= a[i]
    invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
  {
    i := i + 1;
  }
}
method FindZero(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
{
  index := 0;
  while index < a.Length
    invariant 0 <= index
    invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0
  {
    if a[index] == 0 { return; }
    SkippingLemma(a, index);
    index := index + a[index];
  }
  index := -1;
}
```

The first invariant gives the bound on the current element, if we haven't
run into the end of the array already. For each index past `j` (of which there are
`i-j`), the array can be one smaller, so this value is subtracted from `a[j]`.
This only says that the current element cannot be zero, so without the second
invariant, Dafny would not be able to know that there were no zeros. Dafny forgets
everything about the executions of the loop except what is given in the invariants,
so we need to build up the fact that there were no zeros anywhere so far.

That's it! The body of the loop just increments the counter. As we saw
before, Dafny is able to figure out each step on its own, so we don't need to
do anything further. We just needed to give it the structure of the proof it needed
to make. Sometimes the individual steps themselves are complex enough that they need
their own little subproofs, using either a series of assert statements or a whole
other lemma.

When working with arrays, iteration is a natural solution to many problems.
There are some times, however, when recursion is used to define functions or
properties. In these cases, the lemmas usually have the same recursive structure.
To see an example of this, we will consider the problem of counting.

## Counting

We will count the number of `true`s in a sequence of
`bool`s, using the `count` function, given below:

<!-- %check-verify -->
```dafny
function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
  (if a[0] then 1 else 0) + count(a[1..])
}
method m()
{
  assert count([]) == 0;
  assert count([true]) == 1;
  assert count([false]) == 0;
  assert count([true, true]) == 2;
}
```

The code is very straightforward, but one thing to notice
is that the function is defined recursively. Recursive functions like this are prone
to requiring lemmas. There is a desirable property of count that we would like to be
able to use in verifying a program that uses this function: it distributes
over addition. By this we mean:

<!-- %no-check -->
```dafny
forall a, b :: count(a + b) == count(a) + count(b)
```

Here, the first plus (`+`) is sequence concatenation, and the second
is integer addition. Clearly, we can break any sequence into two sequences `a`
and `b`, count them separately, and add the results. This is true, but Dafny
cannot prove it directly. The problem is that the function does not split the sequence
in this way. The function takes the first element, computes its count, then adds it to
the rest of the sequence. If `a` is long, then it can be a while before this
unrolling process actually reaches `count(b)`, so Dafny does not attempt to unwrap
more than a few recursive calls. (Two, to be exact. See the paper
_Computing with an SMT solver_ by Amin, Leino, and Rompf, TAP 2014.)
This is an example of a property that requires a lemma to demonstrate.

In our case, we have two options for the lemma: we could write the same universal quantifier
we had above, or we could make the lemma specific to a pair of sequences `a` and `b`.
It turns out that when we want the distributive property, we don't need the full universal property.
We are just interested in the fact that `count(a + b) == count(a) + count(b)` for two
*specific* `a` and `b` that are known in the program. Thus when we invoke
the lemma to get the property, we can tell it which two sequences we are interested in. If we have
different sequences somewhere else, we can call the method with different arguments, just
like a regular method. It turns out that proving the full universal property, while possible,
is more work than proving the concrete, specific case, so we will tackle this case first.

Thus the lemma should take as arguments the sequences of interest, and the postcondition is
as follows:

<!-- %check-verify Lemmas.5.expect -->
```dafny
lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
  ensures count(a + b) == count(a) + count(b)
{
}
function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
  (if a[0] then 1 else 0) + count(a[1..])
}
```

## Proving the Distributive Property

In order to write the lemma, we have to figure out a strategy for proving it. As you can
verify above (no pun intended), the lemma does not work yet, as otherwise a lemma would be
unnecessary. To do this, we note that the reason that Dafny could not prove this in the
first place is that the `count` function is defined from the start of the sequence,
while the distributive property operates on the middle of a sequence. Thus if we can find
a way to work from the front of the sequence, then Dafny can follow along using the definition
of the function directly.
Well, what is the first element of the sequence? There are a few cases, based on which (if any) of
`a` and `b` are the empty sequence. Thus our lemma will have to consider multiple cases, a common
trait of lemmas. We notice that if `a == []`, then `a + b == b`, regardless of what
`b` is. Lemmas handle cases using the same thing code does to handle cases: if statements. A short
proof of the desirable property is given using asserts below.

<!-- %check-verify Lemmas.6.expect -->
```dafny
lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
  ensures count(a + b) == count(a) + count(b)
{
  if a == [] {
    assert a + b == b;
    assert count(a) == 0;
    assert count(a + b) == count(b);
    assert count(a + b) == count(a) + count(b);
  } else {
    //...
  }
}
function count(a: seq<bool>): nat
{
  if |a| == 0 then 0
  else (if a[0] then 1 else 0) + count(a[1..])
}
```

We can test our lemma in this case by adding a requires clause that restricts `a` to this
case. We find that the code verifies. This means that if `a == []`, then our lemma will
correctly prove the postcondition. In this case, only the first assertion above is necessary;
Dafny gets the rest of the steps on its own (try it!). Now we can consider the other case, when
`0 < |a|`.


Our goal is to relate `count(a + b)` to `count(a)` and `count(b)`. If `a`
is not the empty sequence, then when we employ our trick of following the definition to expand
`count(a + b)`, we get:

<!-- %check-verify -->
```dafny
function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
    (if a[0] then 1 else 0) + count(a[1..])
}
method m2(a: seq<bool>, b:seq<bool>)
  requires |a| > 0
{
  assert a + b == [a[0]] + (a[1..] + b);
  assert count(a + b) == count([a[0]]) + count(a[1..] + b);
}
```

Notice that we get `count([a[0]])` and `a[1..]`. These two terms would also appear
if we expanded `count(a)`. Specifically:

<!-- %check-verify -->
```dafny
method m2(a: seq<bool>, b:seq<bool>)
  requires |a| > 0
{
  assert count(a) == count([a[0]]) + count(a[1..]);
}
function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
    (if a[0] then 1 else 0) + count(a[1..])
}
```

Finally, we can substitute this definition for `count(a)` into the postcondition
to get:

<!-- %no-check -->
```dafny
  assert count(a + b) == count(a) + count(b); // postcondition
  assert count(a + b) == count([a[0]]) + count(a[1..]) + count(b);
```

Now this looks very similar to the expression we got after expanding `count(a + b)`.
The only difference is that `count(a[1..] + b)` has become `count(a[1..]) + count(b)`.
But this is exactly the property we are trying to prove!


## Induction

The argument we are trying to make is *inductive*. We can prove our goal given
that a smaller version of the problem is true. This is precisely the concept of induction:
use a smaller version of a problem to prove a larger one. To do this, we call the recursive
property from within our code. It is a method, so it can be invoked whenever we need it.

Dafny will assume that the recursive call satisfies the specification. This is the inductive
hypothesis, that all recursive calls of the lemma are valid. This depends crucially on the fact that
Dafny also proves termination. This means that eventually, the lemma won't make another recursive call. In
this instance, this is the first branch of the if statement. If there is no recursive call, then
the lemma must be proven directly for that case. Then each call in the stack is justified in assuming
the lemma works for the smaller case. If Dafny did not prove the chain terminated, then the chain could
continue forever, and the assumption for each call would not be justified.

Induction in general is finding a way to build your goal
one step at a time. Viewed another way, it is proving your goal in terms of a smaller version. The distributive
lemma is proven by deconstructing the concatenated sequence one element at a time until the first sequence
is entirely gone. This case is proven as a base case, and then the whole chain of deconstructions is verified.

The key to making this work is that Dafny never has to consider the whole chain of calls. By checking
termination, it can get the chain is finite. Then all it has to do is check one step. If one arbitrary step
is valid, then the whole chain must be as well. This is the same logic that Dafny uses for loops: check that
the invariant holds initially, and that one arbitrary step preserves it, and you have checked the whole loop,
regardless of how many times the loop goes around. The similarity is more than superficial. Both kinds of lemmas
(and both kinds of reasoning Dafny makes about your program) are *inductive*. It is also not surprising
given the relationship between iteration and recursion as two means of achieving the same thing.

With this in mind, we can complete the lemma by calling the lemma recursively in the else branch of the
if statement:

<!-- %check-verify -->
```dafny
lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
  ensures count(a + b) == count(a) + count(b)
{
  if a == [] {
    assert a + b == b;
  } else {
    DistributiveLemma(a[1..], b);
    assert a + b == [a[0]] + (a[1..] + b);
  }
}
function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
    (if a[0] then 1 else 0) + count(a[1..])
}
```

Now the lemma verifies. But what if we wanted to express that every pair of sequences is related in
this way? We must look at another use of lemmas in Dafny in order to be able to do this, which
we will explore with another example.

## Paths In a Directed Graph

As a final, and more advanced, example, we will prove a property about paths in a directed graph.
For this, we will have occasion to call a lemma universally on all sequences of nodes.
A directed graph is composed
of a number of `Node`s, each with some links to other `Node`s. These links are single directional,
and the only restriction on them is that a node cannot link to itself. Nodes are defined as:

<!-- %check-verify -->
```dafny
class Node
{
  // a single field giving the nodes linked to
  var next: seq<Node>
}
```

We represent a graph as a set of Nodes that only point to other nodes in the graph, and not to itself.
We call such a set of nodes *closed*:

<!-- %check-verify -->
```dafny
class Node
{
  // a single field giving the nodes linked to
  var next: seq<Node>
}
predicate closed(graph: set<Node>)
  reads graph
{
  forall i :: i in graph ==>
    forall k :: 0 <= k < |i.next| ==> i.next[k] in graph && i.next[k] != i
}
```

We represent a path as a nonempty sequence of nodes, where each node is linked to by the previous node in the
path. We define two predicates, one that defines a valid path, and another that determines whether the given
path is a valid one between two specific nodes in the graph:

<!-- %check-verify -->
```dafny
class Node
{
  // a single field giving the nodes linked to
  var next: seq<Node>
}
predicate closed(graph: set<Node>)
  reads graph
{
  forall i :: i in graph ==>
    forall k :: 0 <= k < |i.next| ==> i.next[k] in graph && i.next[k] != i
}
predicate pathSpecific(p: seq<Node>, start: Node, end: Node, graph: set<Node>)
  requires closed(graph)
  reads graph
{
  0 < |p| && // path is nonempty
  start == p[0] && end == p[|p|-1] && // it starts and ends correctly
  path(p, graph) // and it is a valid path
}
predicate path(p: seq<Node>, graph: set<Node>)
  requires closed(graph) && 0 < |p|
  reads graph
{
  p[0] in graph &&
    (|p| > 1 ==> p[1] in p[0].next && // the first link is valid, if it exists
                 path(p[1..], graph)) // and the rest of the sequence is a valid path
}
```

Now we are ready to state the lemma we want to prove. We consider a graph and a *sub-graph*: a subset
of the nodes of the graph which also forms a graph. This sub-graph must be *closed*, i.e. not contain links
outside of itself. If we have such a situation, then there cannot be a valid path from a node in the sub-graph
to a node outside this sub-graph. We will call this fact the Closed Lemma, which we state in Dafny as follows:

<!-- %check-verify Lemmas.7.expect -->
```dafny
lemma ClosedLemma(subgraph: set<Node>, root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !(exists p: seq<Node> :: pathSpecific(p, root, goal, graph))
{
  //...
}
class Node
{
  var next: seq<Node>
}
predicate pathSpecific(p: seq<Node>, start: Node, end: Node, graph: set<Node>)
  requires closed(graph)
  reads graph
{
  0 < |p| && // path is nonempty
  start == p[0] && end == p[|p|-1] && // it starts and ends correctly
  path(p, graph) // and it is a valid path
}
predicate path(p: seq<Node>, graph: set<Node>)
  requires closed(graph) && 0 < |p|
  reads graph
{
  p[0] in graph &&
    (|p| > 1 ==> p[1] in p[0].next && // the first link is valid, if it exists
                 path(p[1..], graph)) // and the rest of the sequence is a valid path
}
predicate closed(graph: set<Node>)
  reads graph
{
  forall i :: i in graph ==> forall k :: 0 <= k < |i.next| ==> i.next[k] in graph && i.next[k] != i
}
```

The preconditions state all the requirements: that both the graph and sub-graph are valid,
that the root node is in the sub-graph but the goal isn't, and that everything is contained in
the main graph. The postcondition states that there is no valid path from the root to the goal.
Here we only prove it for a specific pair of start/end nodes.

One way of proving the non-existence of something is to prove given any sequence of nodes that
it cannot be a valid path. We can do this with, you guessed it, another lemma. This lemma will
prove for any given sequence, that it cannot be a valid path from `root` to `goal`.
The disproof of a path lemma looks like:

<!-- %check-verify Lemmas.8.expect -->
```dafny
lemma DisproofLemma(p: seq<Node>, subgraph: set<Node>,
                    root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !pathSpecific(p, root, goal, graph)
{
}
class Node
{
  var next: seq<Node>
}
predicate pathSpecific(p: seq<Node>, start: Node, end: Node, graph: set<Node>)
  requires closed(graph)
  reads graph
{
  0 < |p| && // path is nonempty
  start == p[0] && end == p[|p|-1] && // it starts and ends correctly
  path(p, graph) // and it is a valid path
}
predicate path(p: seq<Node>, graph: set<Node>)
  requires closed(graph) && 0 < |p|
  reads graph
{
  p[0] in graph &&
    (|p| > 1 ==> p[1] in p[0].next && // the first link is valid, if it exists
                 path(p[1..], graph)) // and the rest of the sequence is a valid path
}
predicate closed(graph: set<Node>)
  reads graph
{
  forall i :: i in graph ==> forall k :: 0 <= k < |i.next| ==> i.next[k] in graph && i.next[k] != i
}
```

The preconditions are the same as `ClosedLemma`.  To use `DisproofLemma` in `ClosedLemma`, we need
to invoke it once for every sequence of nodes.  This can be done with Dafny's `forall` statement,
which aggregates the effect of its body for all values of the given bound variable.

<!-- %check-verify Lemmas.9.expect -->
```dafny
lemma ClosedLemma(subgraph: set<Node>, root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !(exists p: seq<Node> :: pathSpecific(p, root, goal, graph))
{
  forall p: seq<Node> {
    DisproofLemma(p, subgraph, root, goal, graph);
  }
}
lemma DisproofLemma(p: seq<Node>, subgraph: set<Node>,
                    root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !pathSpecific(p, root, goal, graph)
{
}
class Node
{
  var next: seq<Node>
}
predicate pathSpecific(p: seq<Node>, start: Node, end: Node, graph: set<Node>)
  requires closed(graph)
  reads graph
{
  0 < |p| && // path is nonempty
    start == p[0] && end == p[|p|-1] && // it starts and ends correctly
    path(p, graph) // and it is a valid path
}
predicate path(p: seq<Node>, graph: set<Node>)
  requires closed(graph) && 0 < |p|
  reads graph
{
  p[0] in graph &&
    (|p| > 1 ==> p[1] in p[0].next && // the first link is valid, if it exists
                 path(p[1..], graph)) // and the rest of the sequence is a valid path
}
predicate closed(graph: set<Node>)
  reads graph
{
  forall i :: i in graph ==> forall k :: 0 <= k < |i.next| ==> i.next[k] in graph && i.next[k] != i
}
```

As you can see, this causes the `ClosedLemma` to verify, so our test of the lemma is
successful. Thus `DisproofLemma` is strong enough, and our work is reduced to just proving
it.

There are a few different ways that a sequence of nodes can be an invalid path. If the path is empty,
then it cannot be a valid path. Also, the first element of the path must be `root` and the last
element needs to be `goal`. Because `root in subgraph` and `goal !in subgraph`, we must
have `root != goal`, so the sequence must have at least two elements. To check that Dafny sees this,
we can temporarily put preconditions on our lemma as follows:

<!-- %check-verify Lemmas.10.expect -->
```dafny
lemma DisproofLemma(p: seq<Node>, subgraph: set<Node>,
                    root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  requires |p| < 2 || p[0] != root || p[|p|-1] != goal
  ensures !pathSpecific(p, root, goal, graph)
{
}
lemma ClosedLemma(subgraph: set<Node>, root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !(exists p: seq<Node> :: pathSpecific(p, root, goal, graph))
{
  forall p: seq<Node> {
    DisproofLemma(p, subgraph, root, goal, graph);
  }
}
class Node
{
  var next: seq<Node>
}
predicate pathSpecific(p: seq<Node>, start: Node, end: Node, graph: set<Node>)
  requires closed(graph)
  reads graph
{
  0 < |p| && // path is nonempty
    start == p[0] && end == p[|p|-1] && // it starts and ends correctly
    path(p, graph) // and it is a valid path
}
predicate path(p: seq<Node>, graph: set<Node>)
  requires closed(graph) && 0 < |p|
  reads graph
{
  p[0] in graph &&
    (|p| > 1 ==> p[1] in p[0].next && // the first link is valid, if it exists
                 path(p[1..], graph)) // and the rest of the sequence is a valid path
}
predicate closed(graph: set<Node>)
  reads graph
{
  forall i :: i in graph ==> forall k :: 0 <= k < |i.next| ==> i.next[k] in graph && i.next[k] != i
}
```

Note that this will cause `ClosedLemma` to stop verifying, as the lemma now only works for some
sequences. We will ignore `ClosedLemma` until we have finished `DisproofLemma`. This verifies,
which means that Dafny is able to prove the postcondition in these circumstances. Thus we only need to
prove that the path is invalid when these conditions do not hold. We can use an `if` statement to express
this:

<!-- %no-check -->
```dafny
if 1 < |p| && p[0] == root && p[|p|-1] == goal {
  (further proof)
}
```

If the path is at least two elements long, the first element is `root`, and the last is
`goal`, then we have a further proof. If these conditions are not met (that is, if the guard of
the `if` statement is false and control continues in the implicit else branch), Dafny will prove
the postcondition on its own (Advanced Remark: you can check this by temporarily adding
the statement `assume false;` inside the then branch of the `if`).
Now we just need to fill in the further proof part. In doing so, we can assume the guard condition
of the `if` statement. We can now use the same inductive trick as above.

If the sequence starts at `root` and ends at `goal`, it cannot be valid because the
sequence must at some point have a node which is not in the previous nodes next list. When we are
given any particular sequence like this, we can break it into two cases: either the sequence is invalid
in the link from the first node to the second, or it is broken somewhere down the line. Just like in the
counting example, Dafny can see that if the first to second node link is not valid, then the sequence
cannot be a path because this mirrors the definition of `path`. Thus we only have further work to do
if the first link is valid. We can express this with another `if` statement:

<!-- %no-check -->
```dafny
if 1 < |p| && p[0] == root && p[|p|-1] == goal {
  if p[1] in p[0].next {
    (yet further proof)
  }
}
```

Here comes the induction. We know that `p[0] == root` and `p[1] in p[0].next`. We also know from
the preconditions that `root in subgraph`. Thus, because `closed(subgraph)`, we know that
`p[1] in subgraph`. These are the same conditions that we started with! What we have here is a smaller
version of the same problem. We can just recursively call `DisproofLemma` to prove that `p[1..]` is
not a path. This means, per the definition of `path`, that `p` cannot be a path, and the second postcondition
is satisfied. This can be implemented as:

<!-- %check-verify -->
```dafny
lemma DisproofLemma(p: seq<Node>, subgraph: set<Node>,
                    root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !pathSpecific(p, root, goal, graph)
{
  if 1 < |p| && p[0] == root && p[|p|-1] == goal {
    if p[1] in p[0].next {
      DisproofLemma(p[1..], subgraph, p[1], goal, graph);
    }
  }
}
lemma ClosedLemma(subgraph: set<Node>, root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !(exists p: seq<Node> :: pathSpecific(p, root, goal, graph))
{
  forall p: seq<Node> {
    DisproofLemma(p, subgraph, root, goal, graph);
  }
}
class Node
{
  var next: seq<Node>
}
predicate pathSpecific(p: seq<Node>, start: Node, end: Node, graph: set<Node>)
  requires closed(graph)
  reads graph
{
  0 < |p| && // path is nonempty
    start == p[0] && end == p[|p|-1] && // it starts and ends correctly
    path(p, graph) // and it is a valid path
}
predicate path(p: seq<Node>, graph: set<Node>)
  requires closed(graph) && 0 < |p|
  reads graph
{
  p[0] in graph &&
    (|p| > 1 ==> p[1] in p[0].next && // the first link is valid, if it exists
                 path(p[1..], graph)) // and the rest of the sequence is a valid path
}
predicate closed(graph: set<Node>)
  reads graph
{
  forall i :: i in graph ==> forall k :: 0 <= k < |i.next| ==> i.next[k] in graph && i.next[k] != i
}
```

Now `DisproofLemma` verifies, and with the removal of the testing preconditions, we see that
`ClosedLemma` verifies as well. We have thus proven that there cannot be a path from inside a closed
sub-graph to outside.

The `forall` statement is useful when a lemma needs to be instantiated an unbounded number of times.
The example showed a simple version of the `forall` statement.  For more advanced versions, see,
for example, _Well-founded Functions and Extreme Predicates in Dafny: A Tutorial_ by Leino, IWIL-2015,
or examples in the Dafny test suite.

Always
remember to check that your lemma is sufficient to prove what you need. Nothing is more frustrating than
spending a while making a lemma verify, only to find out you need something stronger. This also lets you
avoid creating a lemma with a precondition that is so restrictive that you cannot call it where you need to.
