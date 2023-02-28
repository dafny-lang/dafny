// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Problem 2 concerns an interpreter for the language of S and K combinators.

// -----------------------------------------------------------------------------
// Definitions

// First, we define the language of combinator terms.  "Apply(x, y)" is what
// the problem description writes as "(x y)".  In the following Dafny
// definition, "car" and "cdr" are declared to be destructors for terms
// constructed by Apply.

datatype Term = S | K | Apply(car: Term, cdr: Term)

// The problem defines values to be a subset of the terms.  More precisely,
// a Value is a Term that fits the following grammar:
//     Value = K | S | (K Value) | (S Value) | ((S Value) Value)
// The following predicate says whether or not a given term is a value.

function method IsValue(t: Term): bool
  ensures IsValue(t) && t.Apply? ==> IsValue(t.car) && IsValue(t.cdr);
{
  match t
  case K => true
  case S => true
  case Apply(a, b) =>
    match a
    case K =>
      assert IsValue(a);
      IsValue(b)
    case S =>
      assert IsValue(a);
      IsValue(b)
    case Apply(x, y) =>
      assert x==S && IsValue(y) && IsValue(b) ==> IsValue(a);
      x==S && IsValue(y) && IsValue(b)
}

// A context is essentially a term with one missing subterm, a "hole".  It
// is defined as follows:

datatype Context = Hole | C_term(Context, Term) | value_C(Term/*Value*/, Context)

// The problem seems to suggest that the value_C form requires a value and
// a context.  To formalize that notion, we define a predicate that checks this
// condition.

function IsContext(C: Context): bool
{
  match C
  case Hole => true                                   // []
  case C_term(D, t) => IsContext(D)                   // (D t)
  case value_C(v, D) => IsValue(v) && IsContext(D)    // (v D)
}

// The EvalExpr function replace the hole in a context with a given term.

function EvalExpr(C: Context, t: Term): Term
  requires IsContext(C);
{
  match C
  case Hole => t
  case C_term(D, u) => Apply(EvalExpr(D, t), u)
  case value_C(v, D) => Apply(v, EvalExpr(D, t))
}

// A term can be reduced.  This reduction operation is defined via
// a single-step reduction operation.  In the problem, the single-step
// reduction has the form:
//   C[t] --> C[r]
// We formalize the single-step reduction by a function Step, which
// performs the reduction if it applies or just returns the given term
// if it does.  We will say that "Step applies" to refer to the first
// case, which is a slight abuse of language, since the function "Step"
// is total.
//
// Since the context C is the same on both sides in the single-step
// reduction above, we don't pass it to function Step.  Rather, Step
// just takes a term "t" and returns the following:
//     match t
//     case ((K v1) v2) => v1
//     case (((S v1) v2) v3) => ((v1 v3) (v2 v3))
//     else t
// As you can see below, it takes more lines than shown here to express
// this matching in Dafny, but this is all that Step does.
//
// Again, note that Step returns the given term if neither or the two
// vs in the problem statement applies.
//
// One more thing:  Step has a postcondition (and the body of Step
// contains three asserts that act as lemmas in proving the postcondition).
// The postcondition has been included for the benefit of Verification
// Task 2, and we describe the functions used in the Step postcondition
// only much later in this file.  For now, the postcondition can be
// ignored, since it is, after all, just a consequence of the body
// of Step.

function method Step(t: Term): Term
  ensures !ContainsS(t) ==>
             !ContainsS(Step(t)) &&
             (Step(t) == t || TermSize(Step(t)) < TermSize(t));
{
  match t
  case S => t
  case K => t
  case Apply(x, y) =>
    match x
    case S => t
    case K => t
    case Apply(m, n) =>
      if m == K && IsValue(n) && IsValue(y) then
        assert {:focus} t == Apply(Apply(K, n), y);
        assert !ContainsS(t) ==> !ContainsS(x);
        assert TermSize(n) < TermSize(Apply(m, n));
        n
      else if m.Apply? && m.car == S && IsValue(m.cdr) && IsValue(n) && IsValue(y) then
        assert {:focus} t == Apply(Apply(Apply(S, m.cdr), n), y);
        assert ContainsS(m) && ContainsS(t);
        Apply(Apply(m.cdr, y), Apply(n, y))
      else
        t
}

// The single-step reduction operation may be applied to any subexpression
// of a term that could be considered a hole.  Function FindAndStep
// searches for a (context, term) pair C[u] that denotes a given term "t"
// such that Step applies to "u".  If found, the function returns
// C[Step(u)], which will necessarily be different from "t".  If no such
// C[u] pair exists, this function returns the given "t".
//
// Note, FindAndStep only applies one Step.  We will get to repeated
// applications of steps in the "reduction" method below.
//
// For all definitions above, it was necessary to check (manually) that
// they correspond to the definitions intended in the problem statement.
// That is, the definitions above are all part of the specification.
// For function FindAndStep, the definition given does not require
// such scrutiny.  Rather, we will soon state a theorem that states
// the properties of what FindAndStep returns.
//
// Like Step, FindAndStep has a postcondition, and it is also included to
// support Verification Task 2.

function method FindAndStep(t: Term): Term
  ensures !ContainsS(t) ==>
             !ContainsS(FindAndStep(t)) &&
             (FindAndStep(t) == t || TermSize(FindAndStep(t)) < TermSize(t));
{
  if Step(t) != t then
    Step(t)
  else if !t.Apply? then
    t
  else if FindAndStep(t.car) != t.car then
    Apply(FindAndStep(t.car), t.cdr)
  else if IsValue(t.car) && FindAndStep(t.cdr) != t.cdr then
    Apply(t.car, FindAndStep(t.cdr))
  else
    t
}

// One part of the correctness of FindAndStep (and, indeed, of method
// "reduction" below) is that a term can be terminal, meaning that there is
// no way to apply Step to any part of it.

function IsTerminal(t: Term): bool
{
  !(exists C,u :: IsContext(C) && t == EvalExpr(C,u) && Step(u) != u)
}

// The following theorem states the correctness of the FindAndStep function:

lemma Theorem_FindAndStep(t: Term)
  // If FindAndStep returns the term it started from, then there is no
  // way to take a step.  More precisely, there is no C[u] == t for which the
  // Step applies to "u".
  ensures FindAndStep(t) == t ==> IsTerminal(t);
  // If FindAndStep returns a term that's different from what it started with,
  // then it chose some C[u] == t for which the Step applies to "u", and then
  // it returned C[Step(u)].
  ensures FindAndStep(t) != t ==>
          exists C,u :: IsContext(C) && t == EvalExpr(C,u) && Step(u) != u &&
                        FindAndStep(t) == EvalExpr(C, Step(u));
{
  // The theorem follows from the following lemma, which itself is proved by
  // induction.
  var r, C, u := Lemma_FindAndStep(t);
}

// This is the lemma that proves the theorem above.  Whereas the theorem talks
// existentially about C and u, the lemma constructs C and u and returns them,
// which is useful in the proof by induction.  The computation inside the
// lemma mimicks that done by function FindAndStep; indeed, the lemma
// computes the value of FindAndStep(t) as it goes along and it returns
// that value.

lemma Lemma_FindAndStep(t: Term) returns (r: Term, C: Context, u: Term)
  ensures r == FindAndStep(t);
  ensures r == t ==> IsTerminal(t);
  ensures r != t ==>
            IsContext(C) && t == EvalExpr(C,u) && Step(u) != u &&
            r == EvalExpr(C, Step(u));
{
  Lemma_ContextPossibilities(t);
  if Step(t) != t {
    // t == Hole[t] and Step applies t.  So, return Hole[Step(t)]
    return Step(t), Hole, t;
  } else if !t.Apply? {
    r := t;
  } else {
    r, C, u := Lemma_FindAndStep(t.car);  // (*)
    if r != t.car {
      // t has the form (a b) where a==t.car and b==t.cdr, and a==C[u] for some
      // context C and some u to which the Step applies.  t can therefore be
      // denoted by (C[u] b) == (C b)[u] and the Step applies to u.  So, return
      // (C b)[Step(u)] == (C[Step(u)] b).  Note that FindAndStep(a)
      // gives C[Step(u)].
      return Apply(r, t.cdr), C_term(C, t.cdr), u;
    } else if IsValue(t.car) {
      r, C, u := Lemma_FindAndStep(t.cdr);
      assert IsTerminal(t.car);  // make sure this is still remembered from (*)

      if r != t.cdr {
        // t has the form (a b) where a==t.car and b==t.cdr and "a" is a Value,
        // and b==C[u] for some context C and some u to which the Step applies.
        // t can therefore be denoted by (a C[u]) == (C a)[u] and the Step
        // applies to u.  So, return (C a)[Step(u)] == (a C[Step(u)]).  Note
        // that FindAndStep(b) gives C[Step(u)].
        return Apply(t.car, r), value_C(t.car, C), u;
      } else {
        forall C,u | IsContext(C) && t == EvalExpr(C,u)
          ensures Step(u) == u;
        {
          // The following assert and the first assert of each "case" are
          // consequences of the Lemma_ContextPossibilities that was invoked
          // above.
          assert t.Apply? && IsValue(t.car);
          match (C) {
            case Hole =>
              assert t == u;
            case C_term(D, bt) =>
              assert bt == t.cdr && t.car == EvalExpr(D, u);
            case value_C(at, D) =>
              assert at == t.car && t.cdr == EvalExpr(D, u);
          }
        }
        r := t;
      }
    } else {
      r := t;
    }
  }
}

// The proof of the lemma above used one more lemma, namely one that enumerates
// lays out the options for how to represent a term as a C[u] pair.

lemma Lemma_ContextPossibilities(t: Term)
  ensures forall C,u :: IsContext(C) && t == EvalExpr(C, u) ==>
    (C == Hole && t == u) ||
    (t.Apply? && exists D :: C == C_term(D, t.cdr) && t.car == EvalExpr(D, u)) ||
    (t.Apply? && IsValue(t.car) &&
        exists D :: C == value_C(t.car, D) && t.cdr == EvalExpr(D, u));
{
  // Dafny's induction tactic rocks
}

// We now define a way to record a sequence of reduction steps.
// IsTrace(trace, t, r) returns true iff "trace" gives witness to a
// sequence of terms from "t" to "r", each term reducing to its
// successor in the trace.

datatype Trace = EmptyTrace | ReductionStep(Trace, Term)

function IsTrace(trace: Trace, t: Term, r: Term): bool
{
  match trace
  case EmptyTrace =>
    t == r
  case ReductionStep(tr, u) =>
    IsTrace(tr, t, u) && FindAndStep(u) == r
}

// Finally, we are ready to give the requested routine "reduction", which
// keeps applying FindAndStep until quiescence, that is, until Step
// no longer applies.
//
// As required by Verification Task 1, the "reduction" method has two
// postconditions.  One says that the term returned, "r", was obtained
// from the original term, "t", by a sequence of reduction steps.  The
// other says that "r" cannot be reduced any further.
//
// Unlike the other competition problems, this one requested code
// (for "reduction") that may not terminate.  In order to allow reasoning
// about algorithms that may never terminate, Dafny has a special loop
// statement (a "while" loop with a declaration "decreases *") that
// thus comes in handy for "reduction".  (Dafny never allows recursion
// to be non-terminating, only these special loops.)  Note that use
// of the special loop statement does not have any effect on the
// specifications of the enclosing method (but this may change in a
// future version of Dafny).

method reduction(t: Term) returns (r: Term)
  // The result was obtained by a sequence of reductions:
  ensures exists trace :: IsTrace(trace, t, r);
  // The result "r" cannot be reduced any further:
  ensures IsTerminal(r);
  decreases *;  // allow this method to diverge
{
  r := t;
  ghost var trace := EmptyTrace;
  while true
    invariant IsTrace(trace, t, r);
    decreases *;  // allow this statement to loop forever
  {
    var u := FindAndStep(r);
    if u == r {
      // we have found a fixpoint
      Theorem_FindAndStep(r);
      return;
    }
    r, trace := u, ReductionStep(trace, r);
  }
}

// -----------------------------------------------------------------------------
// Verification Task 2
//
// This part of the problem asks us to consider the reduction of terms that
// do not contain S.  The following function formalizes what it means for a term
// to contain S:

function method ContainsS(t: Term): bool
{
  match t
  case S => true
  case K => false
  case Apply(x, y) => ContainsS(x) || ContainsS(y)
}

// The verification task itself is to prove that "reduction" terminates on any
// term that does not contain S.  To prove this, we need to supply a loop variant
// for the loop in "reduction".  However, Dafny does not allow one loop to be
// proved to terminate in some cases and allowed not to terminate in other cases.
// There, we meet Verification Task 2 by manually copying the body of "reduction"
// into a new method (called VerificationTask2) and proving that this new method
// terminates.  Of course, Dafny does not check that we copy the body correctly,
// so that needs to be checked by a human.
//
// In method VerificationTask2, we added not just the precondition given in the
// Verification Task and a loop variant, but we also added two loop invariants
// and one more postcondition.  One of the loop invariants keep track of that
// there are no S's.  The other loop invariant and the postcondition are for
// the benefit of Verification Task 3, as we explain later.

method VerificationTask2(t: Term) returns (r: Term)
  requires !ContainsS(t);  // a sufficient condition for termination
  // The result was obtained by a sequence of reductions:
  ensures exists trace :: IsTrace(trace, t, r);
  // The result "r" cannot be reduced any further:
  ensures IsTerminal(r);
  // Later in this file, we define a function TerminatingReduction, and the
  // following postcondition says that TerminatingReduction computes the same
  // term as this method does.
  ensures r == TerminatingReduction(t);
{
  r := t;
  ghost var trace := EmptyTrace;
  while true
    invariant IsTrace(trace, t, r) && !ContainsS(r);
    invariant TerminatingReduction(t) == TerminatingReduction(r);
    decreases TermSize(r);
  {
    var u := FindAndStep(r);
    if u == r {
      // we have found a fixpoint
      Theorem_FindAndStep(r);
      return;
    }
    r, trace := u, ReductionStep(trace, r);
  }
}

// What now follows is the definition TermSize, which is used in the
// loop variant.  When a Step is applied to a term without S, TermSize
// is reduced, which is stated as a postcondition of both Step and
// FindAndStep.  That postcondition of FindAndStep is used in the
// proof of termination of method VerificationTask2.

// The loop variant is simply the count of nodes in the term:

function TermSize(t: Term): nat
{
  match t
  case S => 1
  case K => 1
  case Apply(x, y) => 1 + TermSize(x) + TermSize(y)
}

// We have already given two methods for computing a reduction:
// method "reduction", which may or may not terminate, and method
// "VerificationTask2", whose precondition is strong enough to let
// us prove that the method will terminate.  The correspondence
// between the two methods is checked by hand, seeing that
// VerificationTask2 includes the postconditions of "reduction" and
// seeing that the code is the same.
//
// We now define a third way of computing reductions, this time
// using a function (not a method).  To prove that this function
// computes the same thing as method VerificationTask2, we had
// added a postcondition to VerificationTask2 above.  This function
// is introduced for the benefit of stating and verifying Verification
// Task 3.

function TerminatingReduction(t: Term): Term
  requires !ContainsS(t);  // a sufficient condition for termination
  decreases TermSize(t);
{
  if FindAndStep(t) == t then
    t  // we have reached a fixpoint
  else
    TerminatingReduction(FindAndStep(t))
}

// -----------------------------------------------------------------------------
// Verification Task 3

// Here is the function "ks" from Verification Task 3.  It produces a particular
// family of terms that contain only Apply and K.  Hence, we can establish, as a
// postcondition of the function, that ks(n) does not contain S.

function method ks(n: nat): Term
  ensures !ContainsS(ks(n));
{
  if n == 0 then K else Apply(ks(n-1), K)
}

// Verification Task 3 is now established by the following theorem.  It says
// that reducing ks(n) results in either K and (K K), depending on the parity
// of n.  The theorem uses function TerminatingReduction to speak of the
// reduction--remember that (by the last postcondition of method
// VerificationTask2) it computes the same thing as method VerificationTask2
// does.

lemma VerificationTask3()
  ensures forall n: nat ::
    TerminatingReduction(ks(n)) == if n % 2 == 0 then K else Apply(K, K);
{
  forall n: nat {
    VT3(n);
  }
}

lemma VT3(n: nat)
  ensures TerminatingReduction(ks(n)) == if n % 2 == 0 then K else Apply(K, K);
{
  // Dafny's (way cool) induction tactic kicks in and proves the following
  // assertion automatically:
  assert forall p {:matchinglooprewrite false} {:induction} :: 2 <= p ==> FindAndStep(ks(p)) == ks(p-2);
  // And then Dafny's (cool beyond words) induction tactic for lemmas kicks
  // in to prove the postcondition.  (If this got you curious, scope out Leino's
  // VMCAI 2012 paper "Automating Induction with an SMT Solver".)
}
