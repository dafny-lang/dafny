# 1. Introduction {#sec-introduction}

Dafny [@Leino:Dafny:LPAR16] is a programming language with built-in specification constructs,
so that verifying a program's correctness with respect to those specifications
is a natural part of writing software.
The Dafny static program verifier can be used to verify the functional
correctness of programs.
This document is a reference manual for the programming language and a user guide
for the `dafny` tool that performs verification and compilation to an
executable form.

The Dafny programming language is designed to support the static
verification of programs. It is imperative, sequential, supports generic
classes, inheritance and abstraction, methods and functions, dynamic allocation, inductive and
coinductive datatypes, and specification constructs. The
specifications include pre- and postconditions, frame specifications
(read and write sets), and termination metrics. To further support
specifications, the language also offers updatable ghost variables,
recursive functions, and types like sets and sequences. Specifications
and ghost constructs are used only during verification; the compiler
omits them from the executable code.

The `dafny` verifier is run as part of the compiler. As such, a programmer
interacts with it in much the same way as with the static type
checker—when the tool produces errors, the programmer responds by
changing the program’s type declarations, specifications, and statements.

(This document typically uses "Dafny" to refer to the programming language
and `dafny` to refer to the software tool that verifies and compiles programs
in the Dafny language.)

The easiest way to try out the Dafny language is to [download the supporting tools and documentation](https://github.com/dafny-lang/dafny/releases) and
run `dafny` on your machine as you follow along with the [Dafny tutorial](../OnlineTutorial/guide).
The `dafny` tool can be run from the command line (on Linux, MacOS, Windows or other platforms) or from IDEs
such as emacs and VSCode, which can provide syntax highlighting and code manipulation capabilities.

The verifier is powered
by [Boogie](http://research.microsoft.com/boogie)
[@Boogie:Architecture;@Leino:Boogie2-RefMan;@LeinoRuemmer:Boogie2]
and [Z3](https://github.com/z3prover) [@deMouraBjorner:Z3:overview].

From verified programs, the `dafny` compiler can produce code for a number
of different backends:
the .NET platform via intermediate C\# files, Java, Javascript, Go, and C++.
Each language provides a basic Foreign Function Interface (through uses of `:extern`)
and a supporting runtime library.

This reference manual for the Dafny verification system is
based on the following references:
[@Leino:Dafny:LPAR16],
[@MSR:dafny:main],
[@LEINO:Dafny:Calc],
[@LEINO:Dafny:Coinduction],
[Co-induction Simply](http://research.microsoft.com/en-us/um/people/leino/papers/krml230.pdf).

The main part of the reference manual is in top down order except for an
initial section that deals with the lowest level constructs.

The details of using (and contributing to) the dafny tool are described in the User Guide ([Section 13](#sec-user-guide)).

## 1.1. Dafny 4.0

The most recent major version of the Dafny language is Dafny 4.0, released in February 2023.
It has some backwards incompatibilities with Dafny 3, as decribed in the [migration guide](https://github.com/dafny-lang/ide-vscode/wiki/Quick-migration-guide-from-Dafny-3.X-to-Dafny-4.0).

Some of the highlights of Dafny 4.0 are
* support for full unicode
TODO

The user documentation has been expanded with more examples, a FAQ, and an error explanation catalog.
There is even a new book, [Program Proofs](https://mitpress.mit.edu/9780262546232/program-proofs/) by Dafny designer Rustan Leino.

The IDE now has a framework for showing error explanation informatino and corresponding quick fixes are
being added, with refactoring operations on the horizon.
MORE TODO

## 1.2. Dafny Example {#sec-example}
To give a flavor of Dafny, here is the solution to a competition problem.

<!-- %check-verify -->
```dafny
// VSComp 2010, problem 3, find a 0 in a linked list and return
// how many nodes were skipped until the first 0 (or end-of-list)
// was found.
// Rustan Leino, 18 August 2010.
//
// The difficulty in this problem lies in specifying what the
// return value 'r' denotes and in proving that the program
// terminates.  Both of these are addressed by declaring a ghost
// field 'List' in each linked-list node, abstractly representing
// the linked-list elements from the node to the end of the linked
// list.  The specification can now talk about that sequence of
// elements and can use 'r' as an index into the sequence, and
// termination can be proved from the fact that all sequences in
// Dafny are finite.
//
// We only want to deal with linked lists whose 'List' field is
// properly filled in (which can only happen in an acyclic list,
// for example).  To that end, the standard idiom in Dafny is to
// declare a predicate 'Valid()' that is true of an object when
// the data structure representing that object's abstract value
// is properly formed.  The definition of 'Valid()' is what one
// intuitively would think of as the ''object invariant'', and
// it is mentioned explicitly in method pre- and postconditions.
//
// As part of this standard idiom, one also declares a ghost
// variable 'Repr' that is maintained as the set of objects that
// make up the representation of the aggregate object--in this
// case, the Node itself and all its successors.

class Node {
  ghost var List: seq<int>
  ghost var Repr: set<Node>
  var head: int
  var next: Node? // Node? means a Node value or null

  predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    1 <= |List| && List[0] == head &&
    (next == null ==> |List| == 1) &&
    (next != null ==>
      next in Repr && next.Repr <= Repr && this !in next.Repr &&
      next.Valid() && next.List == List[1..])
  }

  static method Cons(x: int, tail: Node?) returns (n: Node)
    requires tail == null || tail.Valid()
    ensures n.Valid()
    ensures if tail == null then n.List == [x]
                            else n.List == [x] + tail.List
  {
    n := new Node;
    n.head, n.next := x, tail;
    if (tail == null) {
      n.List := [x];
      n.Repr := {n};
    } else {
      n.List := [x] + tail.List;
      n.Repr := {n} + tail.Repr;
    }
  }
}

method Search(ll: Node?) returns (r: int)
  requires ll == null || ll.Valid()
  ensures ll == null ==> r == 0
  ensures ll != null ==>
            0 <= r && r <= |ll.List| &&
            (r < |ll.List| ==>
              ll.List[r] == 0 && 0 !in ll.List[..r]) &&
            (r == |ll.List| ==> 0 !in ll.List)
{
  if (ll == null) {
    r := 0;
  } else {
    var jj,i := ll,0;
    while (jj != null && jj.head != 0)
      invariant jj != null ==>
            jj.Valid() &&
            i + |jj.List| == |ll.List| &&
            ll.List[i..] == jj.List
      invariant jj == null ==> i == |ll.List|
      invariant 0 !in ll.List[..i]
      decreases |ll.List| - i
    {
      jj := jj.next;
      i := i + 1;
    }
    r := i;
  }
}

method Main()
{
  var list: Node? := null;
  list := list.Cons(0, list);
  list := list.Cons(5, list);
  list := list.Cons(0, list);
  list := list.Cons(8, list);
  var r := Search(list);
  print "Search returns ", r, "\n";
  assert r == 1;
}

```

