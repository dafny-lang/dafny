// RUN: %dafny /compile:0 /rprint:"%t.rprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file is a Dafny encoding of chapter 7 from "Concrete Semantics: With Isabelle/HOL" by
// Tobias Nipkow and Gerwin Klein.

// ----- first, some definitions from chapter 3 -----

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
type vname = string  // variable names

type val = int
type state = map<vname, val>

datatype aexp = N(n: int) | V(x: vname) | Plus(0: aexp, 1: aexp)  // arithmetic expressions
ghost function aval(a: aexp, s: state): val
{
  match a
  case N(n) => n
  case V(x) => if x in s then s[x] else 0
  case Plus(a0, a1) => aval(a0,s ) + aval(a1, s)
}

datatype bexp = Bc(v: bool) | Not(op: bexp) | And(0: bexp, 1: bexp) | Less(a0: aexp, a1: aexp)
ghost function bval(b: bexp, s: state): bool
{
  match b
  case Bc(v) => v
  case Not(b) => !bval(b, s)
  case And(b0, b1) => bval(b0, s) && bval(b1, s)
  case Less(a0, a1) => aval(a0, s) < aval(a1, s)
}

// ----- IMP commands -----

datatype com = SKIP | Assign(vname, aexp) | Seq(com, com) | If(bexp, com, com) | While(bexp, com)

// ----- Big-step semantics -----

least predicate big_step(c: com, s: state, t: state)
{
  match c
  case SKIP =>
    s == t
  case Assign(x, a) =>
    t == s[x := aval(a, s)]
  case Seq(c0, c1) =>
    exists s' ::
    big_step(c0, s, s') &&
    big_step(c1, s', t)
  case If(b, thn, els) =>
    big_step(if bval(b, s) then thn else els, s, t)
  case While(b, body) =>
    (!bval(b, s) && s == t) ||
    (bval(b, s) && exists s' ::
     big_step(body, s, s') &&
     big_step(While(b, body), s', t))
}

lemma Example1(s: state, t: state)
  requires t == s["x" := 5]["y" := 5]
  ensures big_step(Seq(Assign("x", N(5)), Assign("y", V("x"))), s, t)
{
  var s' := s["x" := 5];
  calc <== {
    big_step(Seq(Assign("x", N(5)), Assign("y", V("x"))), s, t);
    // 5 is suffiiently high
    big_step#[5](Seq(Assign("x", N(5)), Assign("y", V("x"))), s, t);
    exists sm ::
      big_step#[4](Assign("x", N(5)), s, sm) && big_step#[4](Assign("y", V("x")), sm, t);
    big_step#[4](Assign("x", N(5)), s, s') && big_step#[4](Assign("y", V("x")), s', t);
    // the rest is done automatically
    true;
  }
}

lemma SemiAssociativity(c0: com, c1: com, c2: com, s: state, t: state)
  ensures big_step(Seq(Seq(c0, c1), c2), s, t) == big_step(Seq(c0, Seq(c1, c2)), s, t)
{
}

ghost predicate equiv_c(c: com, c': com)
{
  forall s,t :: big_step(c, s, t) == big_step(c', s, t)
}

lemma lemma_7_3(b: bexp, c: com)
  ensures equiv_c(While(b, c), If(b, Seq(c, While(b, c)), SKIP))
{
}

lemma lemma_7_4(b: bexp, c: com)
  ensures equiv_c(If(b, c, c), c)
{
}

lemma lemma_7_5(b: bexp, c: com, c': com)
  requires equiv_c(c, c')
  ensures equiv_c(While(b, c), While(b, c'))
{
  forall s,t
    ensures big_step(While(b, c), s, t) == big_step(While(b, c'), s, t)
  {
    if big_step(While(b, c), s, t) {
      lemma_7_6(b, c, c', s, t);
    }
    if big_step(While(b, c'), s, t) {
      lemma_7_6(b, c', c, s, t);
    }
  }
}

least lemma lemma_7_6(b: bexp, c: com, c': com, s: state, t: state)
  requires big_step(While(b, c), s, t) && equiv_c(c, c')
  ensures big_step(While(b, c'), s, t)
{
}

// equiv_c is an equivalence relation
lemma equiv_c_reflexive(c: com, c': com)
  ensures c == c' ==> equiv_c(c, c')
{
}
lemma equiv_c_symmetric(c: com, c': com)
  ensures equiv_c(c, c') ==> equiv_c(c', c)
{
}
lemma equiv_c_transitive(c: com, c': com, c'': com)
  ensures equiv_c(c, c') && equiv_c(c', c'') ==> equiv_c(c, c'')
{
}

lemma IMP_is_deterministic(c: com, s: state, t: state, t': state)
  requires big_step(c, s, t) && big_step(c, s, t')
  ensures t == t'
{
  // If we use iterates indexed by nat (not ORDINAL) and declare this lemma as an
  // "least lemma", then Dafny proves the lemma automatically (Dafny totally rocks!).
  // However, with ORDINAL, we have to supply the .IsLimit case ourselves (well,
  // Dafny is still pretty good).
  var k :| big_step#[k](c, s, t);
  var k' :| big_step#[k'](c, s, t');
  IMP_is_deterministic_Aux(k, k', c, s, t, t');
}
lemma IMP_is_deterministic_Aux(k: ORDINAL, k': ORDINAL, c: com, s: state, t: state, t': state)
  requires big_step#[k](c, s, t) && big_step#[k'](c, s, t')
  ensures t == t'
{
  // Dafny totally rocks!
}

// ----- Small-step semantics -----

least predicate small_step(c: com, s: state, c': com, s': state)
{
  match c
  case SKIP => false
  case Assign(x, a) =>
    c' == SKIP && s' == s[x := aval(a, s)]
  case Seq(c0, c1) =>
    (c0 == SKIP && c' == c1 && s' == s) ||
    exists c0' :: c' == Seq(c0', c1) && small_step(c0, s, c0', s')
  case If(b, thn, els) =>
    c' == (if bval(b, s) then thn else els) && s' == s
  case While(b, body) =>
    c' == If(b, Seq(body, While(b, body)), SKIP) && s' == s
}

// When working with iterates indexed by ORDINAL, it takes a little more effort to
// figure out that the disjuncts of Seq are exclusive, that is, that c0 != SKIP in
// the second case.
lemma SeqCasesAreExclusive(k: ORDINAL, c0: com, c1: com, s: state, c': com, s': state)
  requires k.Offset > 0 && small_step#[k](Seq(c0, c1), s, c', s')
  ensures c0 == SKIP ==> c' == c1 && s' == s
{
  assert k.Offset != 0;
  if c0 == SKIP && k.Offset == 1 {
    assert (c0 == SKIP && c' == c1 && s' == s) || exists c0' :: c' == Seq(c0', c1) && small_step(c0, s, c0', s');
    if {
      case c0 == SKIP && c' == c1 && s' == s =>
        // trivial
      case exists c0' :: c' == Seq(c0', c1) && small_step(c0, s, c0', s') =>
        assert false;  // absurd
    }
  }
}

lemma SmallStep_is_deterministic(cs: (com, state), cs': (com, state), cs'': (com, state))
  requires small_step(cs.0, cs.1, cs'.0, cs'.1)
  requires small_step(cs.0, cs.1, cs''.0, cs''.1)
  ensures cs' == cs''
{
  var k :| small_step#[k](cs.0, cs.1, cs'.0, cs'.1);
  var k' :| small_step#[k'](cs.0, cs.1, cs''.0, cs''.1);
  SmallStep_is_deterministic_Aux(k, k', cs, cs', cs'');
}

lemma SmallStep_is_deterministic_Aux(k: ORDINAL, k': ORDINAL, cs: (com, state), cs': (com, state), cs'': (com, state))
  requires small_step#[k](cs.0, cs.1, cs'.0, cs'.1)
  requires small_step#[k'](cs.0, cs.1, cs''.0, cs''.1)
  ensures cs' == cs''
{
  if k.IsLimit {
    var m :| m < k && small_step#[m](cs.0, cs.1, cs'.0, cs'.1);
    SmallStep_is_deterministic_Aux(m, k', cs, cs', cs'');
  } else if k'.IsLimit {
    var m :| m < k' && small_step#[m](cs.0, cs.1, cs''.0, cs''.1);
    SmallStep_is_deterministic_Aux(k, m, cs, cs', cs'');
  } else {
    match cs.0
    case Assign(x, a) =>
    case Seq(c0, c1) =>
      SeqCasesAreExclusive(k, c0, c1, cs.1, cs'.0, cs'.1);
      SeqCasesAreExclusive(k', c0, c1, cs.1, cs''.0, cs''.1);
      if c0 == SKIP {
      } else {
        var c0' :| cs'.0 == Seq(c0', c1) && small_step#[k-1](c0, cs.1, c0', cs'.1);
        var c0'' :| cs''.0 == Seq(c0'', c1) && small_step#[k'-1](c0, cs.1, c0'', cs''.1);
        SmallStep_is_deterministic_Aux(k-1, k'-1, (c0, cs.1), (c0', cs'.1), (c0'', cs''.1));
      }
    case If(b, thn, els) =>
    case While(b, body) =>
  }
}

least predicate small_step_star(c: com, s: state, c': com, s': state)
{
  (c == c' && s == s') ||
  exists c'', s'' ::
    small_step(c, s, c'', s'') && small_step_star(c'', s'', c', s')
}

lemma star_transitive(c0: com, s0: state, c1: com, s1: state, c2: com, s2: state)
  requires small_step_star(c0, s0, c1, s1) && small_step_star(c1, s1, c2, s2)
  ensures small_step_star(c0, s0, c2, s2)
{
  star_transitive_aux(c0, s0, c1, s1, c2, s2);
}
least lemma star_transitive_aux(c0: com, s0: state, c1: com, s1: state, c2: com, s2: state)
  requires small_step_star(c0, s0, c1, s1)
  ensures small_step_star(c1, s1, c2, s2) ==> small_step_star(c0, s0, c2, s2)
{
}

// The big-step semantics can be simulated by some number of small steps
least lemma BigStep_implies_SmallStepStar(c: com, s: state, t: state)
  requires big_step(c, s, t)
  ensures small_step_star(c, s, SKIP, t)
{
  match c
  case SKIP =>
    // trivial
  case Assign(x, a) =>
    assert small_step_star(SKIP, t, SKIP, t);
  case Seq(c0, c1) =>
    var s' :| big_step(c0, s, s') && big_step(c1, s', t);
    calc <== {
      small_step_star(c, s, SKIP, t);
      { star_transitive(Seq(c0, c1), s, Seq(SKIP, c1), s', SKIP, t); }
      small_step_star(Seq(c0, c1), s, Seq(SKIP, c1), s') && small_step_star(Seq(SKIP, c1), s', SKIP, t);
      { lemma_7_13(c0, s, SKIP, s', c1); }
      small_step_star(c0, s, SKIP, s') && small_step_star(Seq(SKIP, c1), s', SKIP, t);
      //{ BigStep_implies_SmallStepStar(c0, s, s'); }
      small_step_star(Seq(SKIP, c1), s', SKIP, t);
      { assert small_step(Seq(SKIP, c1), s', c1, s'); }
      small_step_star(c1, s', SKIP, t);
      //{ BigStep_implies_SmallStepStar(c1, s', t); }
      true;
    }
  case If(b, thn, els) =>
  case While(b, body) =>
    if !bval(b, s) && s == t {
      calc <== {
        small_step_star(c, s, SKIP, t);
        { assert small_step(c, s, If(b, Seq(body, While(b, body)), SKIP), s); }
        small_step_star(If(b, Seq(body, While(b, body)), SKIP), s, SKIP, t);
        { assert small_step(If(b, Seq(body, While(b, body)), SKIP), s, SKIP, s); }
        small_step_star(SKIP, s, SKIP, t);
        true;
      }
    } else {
      var s' :| big_step(body, s, s') && big_step(While(b, body), s', t);
      calc <== {
        small_step_star(c, s, SKIP, t);
        { assert small_step(c, s, If(b, Seq(body, While(b, body)), SKIP), s); }
        small_step_star(If(b, Seq(body, While(b, body)), SKIP), s, SKIP, t);
        { assert small_step(If(b, Seq(body, While(b, body)), SKIP), s, Seq(body, While(b, body)), s); }
        small_step_star(Seq(body, While(b, body)), s, SKIP, t);
        { star_transitive(Seq(body, While(b, body)), s, Seq(SKIP, While(b, body)), s', SKIP, t); }
        small_step_star(Seq(body, While(b, body)), s, Seq(SKIP, While(b, body)), s') && small_step_star(Seq(SKIP, While(b, body)), s', SKIP, t);
        { lemma_7_13(body, s, SKIP, s', While(b, body)); }
        small_step_star(body, s, SKIP, s') && small_step_star(Seq(SKIP, While(b, body)), s', SKIP, t);
        //{ BigStep_implies_SmallStepStar(body, s, s'); }
        small_step_star(Seq(SKIP, While(b, body)), s', SKIP, t);
        { assert small_step(Seq(SKIP, While(b, body)), s', While(b, body), s'); }
        small_step_star(While(b, body), s', SKIP, t);
        //{ BigStep_implies_SmallStepStar(While(b, body), s', t); }
        true;
      }
    }
}

least lemma lemma_7_13(c0: com, s0: state, c: com, t: state, c1: com)
  requires small_step_star(c0, s0, c, t)
  ensures small_step_star(Seq(c0, c1), s0, Seq(c, c1), t)
{
  if c0 == c && s0 == t {
  } else {
    var c', s' :| small_step(c0, s0, c', s') && small_step_star(c', s', c, t);
    lemma_7_13(c', s', c, t, c1);
  }
}

least lemma SmallStepStar_implies_BigStep(c: com, s: state, t: state)
  requires small_step_star(c, s, SKIP, t)
  ensures big_step(c, s, t)
{
  if c == SKIP && s == t {
  } else {
    var c', s' :| small_step(c, s, c', s') && small_step_star(c', s', SKIP, t);
    SmallStep_plus_BigStep(c, s, c', s', t);
  }
}

least lemma SmallStep_plus_BigStep(c: com, s: state, c': com, s': state, t: state)
  requires small_step(c, s, c', s')
  ensures big_step(c', s', t) ==> big_step(c, s, t)
{
  match c
  case Assign(x, a) =>
  case Seq(c0, c1) =>
    if c0 == SKIP && c' == c1 && s' == s {
    } else {
      var c0' :| c' == Seq(c0', c1) && small_step(c0, s, c0', s');
      if big_step(c', s', t) {
        var s'' :| big_step(c0', s', s'') && big_step(c1, s'', t);
      }
    }
  case If(b, thn, els) =>
  case While(b, body) =>
    assert c' == If(b, Seq(body, While(b, body)), SKIP) && s' == s;
    if big_step(c', s', t) {
      assert big_step(if bval(b, s') then Seq(body, While(b, body)) else SKIP, s', t);
    }
}

// big-step and small-step semantics agree
lemma BigStep_SmallStepStar_Same(c: com, s: state, t: state)
  ensures big_step(c, s, t) <==> small_step_star(c, s, SKIP, t)
{
  if big_step(c, s, t) {
    BigStep_implies_SmallStepStar(c, s, t);
  }
  if small_step_star(c, s, SKIP, t) {
    SmallStepStar_implies_BigStep(c, s, t);
  }
}

ghost predicate final(c: com, s: state)
{
  !exists c',s' :: small_step(c, s, c', s')
}

// lemma 7.17:
lemma final_is_skip(c: com, s: state)
  ensures final(c, s) <==> c == SKIP
{
  if c == SKIP {
    assert final(c, s);
  } else {
    var _, _ := only_skip_has_no_next_state(c, s);
  }
}
lemma only_skip_has_no_next_state(c: com, s: state) returns (c': com, s': state)
  requires c != SKIP
  ensures small_step(c, s, c', s')
{
  match c
  case SKIP =>
  case Assign(x, a) =>
    c', s' := SKIP, s[x := aval(a, s)];
  case Seq(c0, c1) =>
    if c0 == SKIP {
      c', s' := c1, s;
    } else {
      c', s' := only_skip_has_no_next_state(c0, s);
      c' := Seq(c', c1);
    }
  case If(b, thn, els) =>
    c', s' := if bval(b, s) then thn else els, s;
  case While(b, body) =>
    c', s' := If(b, Seq(body, While(b, body)), SKIP), s;
}

lemma lemma_7_18(c: com, s: state)
  ensures (exists t :: big_step(c, s, t)) <==>
          (exists c',s' :: small_step_star(c, s, c', s') && final(c', s'))
{
  if exists t :: big_step(c, s, t) {
    var t :| big_step(c, s, t);
    BigStep_SmallStepStar_Same(c, s, t);
    calc ==> {
      true;
      big_step(c, s, t);
      small_step_star(c, s, SKIP, t);
      { assert final(SKIP, t); }
      small_step_star(c, s, SKIP, t) && final(SKIP, t);
    }
  }
  if exists c',s' :: small_step_star(c, s, c', s') && final(c', s') {
    var c',s' :| small_step_star(c, s, c', s') && final(c', s');
    final_is_skip(c', s');
    BigStep_SmallStepStar_Same(c, s, s');
  }
}

// Autotriggers:0 added as this file relies on proving a property of the form body(f) == f
