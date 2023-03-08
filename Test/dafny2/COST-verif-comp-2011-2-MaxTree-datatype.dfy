// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This Dafny program was inspired by Claude Marche's Why3ML program that solves
// Challenge 2 of the COST Verification Competition.  It particular, it uses an
// inductive datatype for the Tree data structure, and it uses a Contains function
// defined on such trees.  This makes the whole program short and sweet, keeps
// proof annotation overhead to a minimum, and--best of all--makes for a convincing
// specification of Max.
// Rustan Leino, 7 Oct 2011

// Remarks:

// A little detail about the implementation of 'Max' below is that the precondition
// 't != Null' means that the 'match' statement does not need to include a case
// for 'Null'.  The correctness of the omission of cases is checked by the program
// verifier.

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
// verifies and compiles the program (for this program in less than 2 seconds)
// without further human intervention.

datatype Tree = Null | Node(Tree, int, Tree)

ghost function Contains(t: Tree, v: int): bool
{
  match t
  case Null => false
  case Node(left, x, right) => x == v || Contains(left, v) || Contains(right, v)
}

method Max(t: Tree) returns (result: int)
  requires t != Null;
  ensures Contains(t, result) && forall v :: Contains(t, v) ==> v <= result;
{
  match (t) {
    case Node(left, x, right) =>
      result := MaxAux(right, x);
      result := MaxAux(left, result);
  }
}

method MaxAux(t: Tree, acc: int) returns (result: int)
  ensures result == acc || Contains(t, result);
  ensures acc <= result && forall v :: Contains(t, v) ==> v <= result;
{
  match (t) {
    case Null => result := acc;
    case Node(left, x, right) =>
      result := MaxAux(right, if x < acc then acc else x);
      result := MaxAux(left, result);
  }
}
