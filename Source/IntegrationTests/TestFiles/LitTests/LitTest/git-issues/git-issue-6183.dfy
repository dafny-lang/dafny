// RUN: %verify --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Regression test: a looping-trigger subexpression that references a variable bound by a
// binder inside the quantifier body used to be hoisted into the quantifier range by the
// matching-loop rewrite, producing an "undeclared identifier" Boogie resolution error. This
// affects every binder form (match cases, let/such-that, comprehensions, lambdas), in both
// the quantifier's term and its range.

datatype Instr = Branch(m: nat)

// match-bound variable in the term
predicate WellTyped(ii: seq<Instr>, typing: seq<nat>)
  requires forall pc :: 0 <= pc < |ii| ==>
    match ii[pc] case Branch(n) => pc + n < |typing|
{
  forall pc :: 0 <= pc < |ii| ==>
    match ii[pc]
    case Branch(n) =>
      typing[pc + n] == typing[pc]
}

// match-bound variable in the range (guard)
predicate WellTypedRange(ii: seq<Instr>, typing: seq<nat>)
  requires forall pc :: 0 <= pc < |ii| ==> match ii[pc] case Branch(n) => pc + n < |typing|
{
  forall pc | 0 <= pc < |ii| && (match ii[pc] case Branch(n2) => typing[pc + n2] == typing[pc])
    :: true
}

// lambda-bound variable (the binder is self-contained, so the lambda itself remains extractable)
predicate LambdaCase(a: seq<nat>)
  requires forall i :: 0 <= i < |a| ==> ((x: nat) requires i + x < |a| => a[i + x] == a[i])(0)
{
  forall i :: 0 <= i < |a| ==> ((x: nat) requires i + x < |a| => a[i + x] == a[i])(0)
}

// set-comprehension-bound variable in the term
predicate SetComprehensionCase(a: seq<nat>, n: nat)
{
  forall i :: 0 <= i < |a| ==> (set j | 0 <= j < n && i + j < |a| && a[i + j] == a[i]) == {}
}
