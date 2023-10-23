// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(i: int)

method MethodTestNoLeak(x: bool)
  requires r: (x <==> P(12)) && P(12) != P(13)
{
  var result :=
    if x then
      assert p: P(12) by {reveal r;}
      assert p': P(12) by {reveal p, q;} // q not available in this scope
      12
    else
      assert q: P(13) by {reveal r; }
      assert q': P(13) by {reveal p, q;} // p not available in this scope
      13;
  reveal q, p; // Should not resolve
  assert P(12); // If it did resolve, this should fail because we don't know x
  assert P(13); // this should fail because we don't know x
  assert false by { // Otherwise, we might be able to prove false
    reveal r;
  }
}