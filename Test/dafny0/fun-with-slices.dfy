// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This test was contributed by Bryan. It has shown some instabilities in the past.

method seqIntoArray<A>(s: seq<A>, a: array<A>, index: nat)
  requires index + |s| <= a.Length
  modifies a
  ensures  a[..] == old(a[0..index]) + s + old(a[index + |s|..])
{
    var i := index;

    while i < index + |s|
      invariant index <= i <= index + |s| <= a.Length
      invariant a[..] == old(a[..index]) + s[..i - index] + old(a[i..])
    {
        a[i] := s[i - index];
        i := i + 1;
    }
}
