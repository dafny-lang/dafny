// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0 {
  type vname = string
  type state = vname -> int

  // regression: the following used to lead to a crash and malformed Boogie
  lemma L(f: state --> int)
  {
    L(f);  // error: cannot prove termination
  }
}

module M1 {
  type vname = string
  type state = vname -> int
  const Zero: state := s => 0  // regression: parsing had once disallowed arrows
}

module M2 {
  class C {
    static const X: bool := true
  }

  const Y := true

  predicate P(u: int)

  lemma A() {
    forall u: int {  // regression: the inferred "ensures" clause used to have
                     // a problem with static ("const") fields
      B(u);
    }
  }

  lemma B(u: int)
    ensures C.X && Y && P(u)
}
