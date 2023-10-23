// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M0(t: map<int, int>, k: int)
  requires k in t
{
  if * {
    assert |t| == |t - {k}| + 1;
  } else if * {
    assume t.Items == {(1, 2), (3, 4)};
    assert |t| == 2;
  } else {
    assume t.Values == {2, 3, 4};
    assert |t| >= 2;
  }
}

method M0'(t: map<int, int>, k: int)
  requires k in t
{
  if * {
    var _ := |(t - {k}).Keys|;
    assert |t| == |t - {k}| + 1;
  } else if * {
    assume t.Items == {(1, 2), (3, 4)};
    var _ := |t.Items|;
    assert |t| == 2;
  } else {
    assume t.Values == {2, 3, 4};
    assert |t.Values| >= 2;
  }
}
