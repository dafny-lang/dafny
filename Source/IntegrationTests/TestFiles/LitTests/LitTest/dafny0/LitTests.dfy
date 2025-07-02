// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module SeqLength {
  function LengthToIntUp(v: seq<int>): int {
    if v == [] then
      0
    else
      1 + LengthToIntUp(v[1..])
  }

  function LengthToIntDown(v: seq<int>): int {
    if v == [] then
      0
    else
      1 + LengthToIntDown(v[..|v| - 1])
  }

  method TestUp() {
    var j := [2, 3, 5, 7, 11, 13, 17, 19];
    assert LengthToIntUp(j) == 8;
  }

  method TestDown() {
    var j := [2, 3, 5, 7, 11, 13, 17, 19];
    assert LengthToIntDown(j) == 8;
  }

  function ToInt(v: seq<int>): int
    decreases |v|
  {
    if |v| == 0 then
      0
    else
      10 * ToInt(v[..|v| - 1]) + v[|v| - 1]
  }

  function ToIntBackward(v: seq<int>): int
    decreases |v|
  {
    if |v| == 0 then
      0
    else
      v[0] + 10 * ToIntBackward(v[1..])
  }

  method Test() {
    assert ToIntBackward([1, 2]) == 21;
    assert ToIntBackward([1, 2, 3, 4, 5]) == 54321;

    assert ToInt([1, 2]) == 12;
    assert ToInt([1, 2, 3, 4, 5]) == 12345; // error:  verifier runs out of steam :(
  }

  method ManualProof() {
    assert ToInt([1, 2, 3, 4, 5]) == 12345 by {
      var j := [1, 2, 3, 4, 5];
      calc {
        ToInt(j);
        10 * ToInt(j[..4]) + 5;
        { assert j[..4][..3] == j[..3]; }
        100 * ToInt(j[..3]) + 45;
        { assert j[..3][..2] == j[..2]; }
        1000 * ToInt(j[..2]) + 345;
        { assert j[..2][..1] == j[..1]; }
        10_000 * ToInt(j[..1]) + 2345;
      }
    }
  }
}
