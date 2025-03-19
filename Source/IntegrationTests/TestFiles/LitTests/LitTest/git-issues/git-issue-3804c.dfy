// RUN: %exits-with 4 %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(i: int)

function Test(x: bool): int
  requires r: if x then P(1) else P(2)
{
  assert p1: x ==> P(1) by { reveal r; }
  assert p2: !x ==> P(2) by { reveal r; }
  var x :=
    match x {
      case true =>
        assert p11: P(1) by { reveal p1; }
        assert p12: P(1) by { reveal p2; } // Previous assertion is not visible here
        assert P(1) by { reveal p11; } // p11 can be revealed and this assertion is visible outside.
        1
      case false => 
        assert p22: P(2) by { reveal p2; }
        assert p21: P(2) by { reveal p1; } // Previous assertion is not visible here
        assert P(2) by { reveal p21; } // p21 can be revealed and this assertion is visible outside.
        2
    };
  assert P(x);
  x
}