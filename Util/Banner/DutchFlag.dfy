method Main()
{
  var a := new Color[3];
  a[0] := White;
  a[1] := Blue;
  a[2] := Red;
  assert a[..] == [White, Blue, Red];
  DutchFlag(a);
  assert Ordered(a[0], a[1]);
  assert Ordered(a[1], a[2]);
  assert a[..] == [Red, White, Blue];
}

datatype Color = Red | White | Blue

predicate Ordered(c: Color, d: Color)
{
  c == Red ||
  c == d ||
  d == Blue
}

method DutchFlag(a: array<Color>)
  requires a != null modifies a
  ensures forall i,j :: 0 <= i < j < a.Length  ==>  Ordered(a[i], a[j])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var r, w, b := 0, 0, a.Length;
  while w != b
    invariant 0 <= r <= w <= b <= a.Length;
    invariant forall i :: 0 <= i < r ==> a[i] == Red
    invariant multiset(a[..]) == old(multiset(a[..]))
  {   match a[w]
        case Red =>
          a[r], a[w] := a[w], a[r];
          r, w := r + 1, w + 1;
        case White =>
          w := w + 1;
        case Blue =>
          b := b - 1;
          a[w], a[b] := a[b], a[w];
  }
}
