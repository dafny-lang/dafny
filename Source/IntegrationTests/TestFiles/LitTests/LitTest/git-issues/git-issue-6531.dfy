// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The equality axiom of a datatype with a single constructor used to range over every
// datatype value, not only the values of that datatype. Here the solver used the axiom
// of Unit at a value of another datatype, which proved the false postcondition of Bad,
// and with it Contradiction.

datatype Unit = U
datatype R = X | Y(n: nat)
datatype S = S(n: nat)

function F(u: Unit, s: S): R {
  if u == U then (if s.n == 0 then X else Y(0)) else Y(1)
}

function G(us: seq<Unit>, s: S): seq<R> {
  if |us| == 0 then [] else [F(us[0], s)] + G(us[1..], s)
}

// False: G([U], S(1)) == [Y(0)].
lemma {:induction false} Bad(us: seq<Unit>, s: S)
  requires 0 < |us| && s.n <= 1
  ensures G(us, s)[0].X? // error: (but this was once provable, due to a bug)
{
  forall us': seq<Unit>, s': S | 0 < |us'| && s'.n <= 1
    ensures G(us', s') != []
  { }
}

lemma Contradiction() ensures false {
  Bad([U], S(1));
  assert G([U], S(1)) == [F(U, S(1))] + G([], S(1));
}
