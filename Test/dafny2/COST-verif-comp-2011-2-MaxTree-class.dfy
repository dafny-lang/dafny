// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
Rustan Leino, 5 Oct 2011

COST Verification Competition, Challenge 2: Maximum in a tree
http://foveoos2011.cost-ic0701.org/verification-competition

Given: A non-empty binary tree, where every node carries an integer.

Implement and verify a program that computes the maximum of the values
in the tree.

Please base your program on the following data structure signature:

public class Tree {
    int value;
    Tree left;
    Tree right;
}

You may represent empty trees as null references or as you consider
appropriate.
*/

// Remarks:

// The specification of this program uses the common dynamic-frames idiom in Dafny:  the
// ghost field 'Contents' stores the abstract value of an object, the ghost field 'Repr'
// stores the set of (references to) objects that make up the representation of the object
// (which in this case is the Tree itself plus the 'Repr' sets of the left and right
// subtrees), and a function 'Valid()' that returns 'true' when an object is in a
// consistent state (that is, when an object satisfies the "class invariant").

// The design I used was to represent an empty tree as a Tree object whose left and
// right pointers point to the object iself.  This is convenient, because it lets
// clients of Tree and the implementation of Tree always use non-null pointers to
// Tree objects.

// What needs to be human-trusted about this program is that the 'requires' and
// 'ensures' clauses (that is, the pre- and postconditions, respectively) of
// 'ComputeMax' are correct.  And, since the specification talks about the ghost
// variable 'Contents', one also needs to trust that the 'Valid()' function
// constrains 'Contents' in a way that a human thinks matches the intuitive
// definition of what the contents of a tree is.

// To give a taste of that the 'Valid()' function does not over-constrain the
// object, I have included two instance constructors, 'Empty()' and 'Node(...)'.
// To take this a step further, one could also write a 'Main' method that
// builds somme tree and then calls 'ComputeMax', but I didn't do that here.

// About Dafny:
// As always (when it is successful), Dafny verifies that the program does not
// cause any run-time errors (like array index bounds errors), that the program
// terminates, that expressions and functions are well defined, and that all
// specifications are satisfied.  The language prevents type errors by being type
// safe, prevents dangling pointers by not having an "address-of" or "deallocate"
// operation (which is accommodated at run time by a garbage collector), and
// prevents arithmetic overflow errors by using mathematical integers (which
// is accommodated at run time by using BigNum's).  By proving that programs
// terminate, Dafny proves that a program's time usage is finite, which implies
// that the program's space usage is finite too.  However, executing the
// program may fall short of your hopes if you don't have enough time or
// space; that is, the program may run out of space or may fail to terminate in
// your lifetime, because Dafny does not prove that the time or space needed by
// the program matches your execution environment.  The only input fed to
// the Dafny verifier/compiler is the program text below; Dafny then automatically
// verifies and compiles the program (for this program in less than 2.5 seconds)
// without further human intervention.

class Tree {
  // an empty tree is represented by a Tree object with left==this==right
  var value: int
  var left: Tree?
  var right: Tree?

  ghost var Contents: seq<int>
  ghost var Repr: set<object>
  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    left != null && right != null &&
    ((left == this == right && Contents == []) ||
     (left in Repr && left.Repr <= Repr && this !in left.Repr &&
      right in Repr && right.Repr <= Repr && this !in right.Repr &&
      left.Valid() && right.Valid() &&
      Contents == left.Contents + [value] + right.Contents))
  }

  function IsEmpty(): bool
    requires Valid();
    reads this, Repr;
    ensures IsEmpty() <==> Contents == [];
  {
    left == this
  }

  constructor Empty()
    ensures Valid() && Contents == [];
  {
    left, right := this, this;
    Contents := [];
    Repr := {this};
  }

  constructor Node(lft: Tree, val: int, rgt: Tree)
    requires lft.Valid() && rgt.Valid();
    ensures Valid() && Contents == lft.Contents + [val] + rgt.Contents;
  {
    left, value, right := lft, val, rgt;
    Contents := lft.Contents + [val] + rgt.Contents;
    Repr := lft.Repr + {this} + rgt.Repr;
  }

  lemma exists_intro<T>(P: T ~> bool, x: T)
    requires P.requires(x)
    requires P(x)
    ensures exists y :: P.requires(y) && P(y)
  {
  }

  method ComputeMax() returns (mx: int)
    requires Valid() && !IsEmpty();
    ensures forall x :: x in Contents ==> x <= mx;
    ensures exists x :: x in Contents && x == mx;
    decreases Repr;
  {
    mx := value;

    if (!left.IsEmpty()) {
      var m := left.ComputeMax();
      mx := if mx < m  then m else mx;
    }

    if (!right.IsEmpty()) {
      var m := right.ComputeMax();
      mx := if mx < m then m else mx;
    }

    exists_intro(x reads this => x in Contents && x == mx, mx);
  }
}
