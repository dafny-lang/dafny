// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(i: int)

method Test(x: bool)
  requires r: if x then P(12) else P(13)
{
  var x :=
    if x then
      assert p: P(12) by {reveal r;} 12
    else
      assert q: P(13) by { reveal r; } 13;
  if * {
    assert P(x) by { // Works
      reveal p, q;
    }
  } else if * {
    assert P(x) by { // Doesn't work
      reveal p;
    }
  } else if * {
    assert P(x) by { // Doesn't work
      reveal q;
    }
  } else if * {
    assert P(x); // Doesn't work
  } else if * {
    reveal p, q;
    assert P(x); // Succeeds
  }
}