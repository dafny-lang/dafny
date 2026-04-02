// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Regression test: single-constructor match inside forall with seq indexing
// using the match-bound variable caused a Boogie resolution error.

datatype Instr = Branch(m: nat)

predicate WellTyped(ii: seq<Instr>, typing: seq<nat>)
  requires forall pc :: 0 <= pc < |ii| ==>
    match ii[pc] case Branch(n) => pc + n < |typing|
{
  forall pc :: 0 <= pc < |ii| ==>
    match ii[pc]
    case Branch(n) =>
      typing[pc + n] == typing[pc]
}
