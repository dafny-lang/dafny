// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Instr = Branch(m: nat)

predicate WellTyped0(ii: seq<Instr>, typing: seq<nat>) {
  forall pc :: 0 <= pc < |ii| ==>
    match ii[pc]
    case Branch(n) =>
      // the following line once crashed Dafny
      typing[pc + n] == typing[pc] // error: index out of bounds
}

predicate WellTyped1(ii: seq<Instr>, typing: seq<nat>) {
  forall pc :: 0 <= pc < |ii| ==>
    match ii[pc]
    case Branch(n) =>
      pc + n < |typing| &&
      typing[pc + n] == typing[pc]
}
