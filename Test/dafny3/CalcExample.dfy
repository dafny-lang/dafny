// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Here is a function "f" and three axioms (that is, unproved lemmas) about "f":

function f(x: int, y: int): int

lemma Associativity(x: int, y: int, z: int)
  ensures f(x, f(y, z)) == f(f(x, y), z)

lemma Monotonicity(y: int, z: int)
  requires y <= z
  ensures forall x :: f(x, y) <= f(x, z)

lemma DiagonalIdentity(x: int)
  ensures f(x, x) == x

// From these axioms, we can prove a lemma about "f":

method CalculationalStyleProof(a: int, b: int, c: int, x: int)
  requires c <= x == f(a, b)
  ensures f(a, f(b, c)) <= x
{
  calc {
    f(a, f(b, c));
  ==  { Associativity(a, b, c); }
    f(f(a, b), c);
  ==  { assert f(a, b) == x; }
    f(x, c);
  <=  { assert c <= x; Monotonicity(c, x); }
    f(x, x);
  ==  { DiagonalIdentity(x); }
    x;
  }
}

// Here's the same lemma, but with a proof written in a different style.
// (An explanation of the constructs in this lemma is found below.)

method DifferentStyleProof(a: int, b: int, c: int, x: int)
  requires A: c <= x
  requires B: x == f(a, b)
  ensures f(a, f(b, c)) <= x
{
  assert 0: f(a, f(b, c)) == f(f(a, b), c) by {
    Associativity(a, b, c);
  }

  assert 1: f(f(a, b), c) == f(x, c) by {
    reveal B;
  }

  assert 2: f(x, c) <= f(x, x) by {
    assert c <= x by { reveal A; }
    Monotonicity(c, x);
  }

  assert 3: f(x, x) == x by {
    DiagonalIdentity(x);
  }

  assert 4: f(a, f(b, c)) == f(x, c) by {
    reveal 0, 1;
  }

  assert 5: f(x, c) <= x by {
    reveal 2, 3;
  }

  assert f(a, f(b, c)) <= x by {
    reveal 4, 5;
  }
}

// To understand the lemma above, here's what you need to know (and then some):
//
// * An ordinary "assert P;" statement instructs the verifier to verify
//   the boolean condition "P" and then to assume "P" from here on (that
//   is, in the control flow that continues from here).
//
// * An assert with a proof is written "assert P by { S }" where "S" is
//   a list of statements (typically other assertions and lemma calls).
//   This statement instructs the verifier to do "S" and then prove "P".
//   Once this is done, the verifier assumes "P" from here on, but it
//   "forgets" anything it learnt or was able to assume on account of
//   doing "S". In other words, an assertion like this is like a local
//   lemma--the proof "S" is used only to establish "P" and is then
//   forgotten, and after the statement, only "P" remains. Note, the
//   body of the "by" clause does "S" and then stops; that is, there are
//   no control paths out of the body of the "by" clause.
//
// * An assertion (either an ordinary assertion or an assertion with a
//   proof) can start with a label, as in:
//
//     assert L: P;
//
//   or:
//
//     assert L: P by { S }
//
//   This instructs the verifier to prove the assertion as described in the
//   previous two bullets, but then to forget about "P". In other words, the
//   difference between a labeled assertion and and an unlabeled assertion
//   is that an unlabeled assertion ends by assuming "P" whereas the labeled
//   assertion does not assume anything.
//
// * Syntactically, the label "L" in a labeled assertion is the same as in
//   a statement prefix "label L:", namely, "L" is either an identifier or
//   a (decimal) numeric literal.
//
// * The condition "P" proved by a labeled assertion can later be recalled
//   using a "reveal" statement. The "reveal" statement takes a list of
//   arguments, each of which can be a label occurring in a previous
//   assertion.
//
// * A precondition (or think of it as an antecedent of a lemma) is given by
//   a "requires" clause. Ordinarily, the precondition is assumed on entry
//   to the body of a method or lemma. Like an assert statement, a precondition
//   can also be labeled. Such a precondition is not automatically assumed on
//   entry to the body, but can be recalled by a "reveal" statement.
//
// * Fine points: Some exclusions apply. For example, labeled preconditions are
//   not supported for functions and cannot be used to hide/reveal conditions
//   while checking the well-formedness of a specification. Labeled assertions are
//   not supported in expression contexts. The "reveal" described is the "reveal"
//   statement. A labeled assertion can be revealed only at those program points
//   that are dominated by the assertion, that is, in places that are reached
//   only after definitely first having reached the assertion.
//
// * Fine point: The label "L" introduced by an assertion can also be used in
//   "old@L(E)" expressions, where "E" is an expression. However, note that
//   "old@L(E)" differs from "E" only in how the heap is dereferenced. That is,
//   "old@L" has no effect on local variables. In contrast, a labeled assertion
//   speaks about the values of the heap and locals at the time the assertion is
//   mentioned. So, even if the heap or locals mentioned in a labeled assertion
//   change after the assertion is mentioned, recalling the assertion condition
//   with a "reveal" statement always recall the condition with the heap and locals
//   as they were when the assert was stated. For example, suppose "P" is an
//   expression that mentions a local variable "x". Then, the second assertion in
//
//     assert L: P by { ... }
//     x := x + 1;
//     ...make changes to the heap...
//     reveal L;
//     assert old@L(P);
//
//   does not necessarily hold. The first assertion uses the initial value of the
//   heap and the initial value of "x". Consequently, "reveal L;" recalls the
//   asserted condition, with that initial heap and that initial value of "x",
//   despite the fact that the code changes both "x" and the heap between the
//   assert and the reveal. The expression "old@L(P)" essentially rolls
//   back to the initial heap, but it uses the current value of "x".
