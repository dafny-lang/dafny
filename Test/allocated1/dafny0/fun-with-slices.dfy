// RUN: %dafny /verifyAllModules /allocated:1 /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This test was contributed by Bryan. It has shown some instabilities in the past.

method seqIntoArray<A>(s: seq<A>, a: array<A>, index: nat)
  requires index + |s| <= a.Length
  modifies a
  ensures a[..] == old(a[..index]) + s + old(a[index + |s|..])
{
  var i := index;

  while i < index + |s|
    invariant index <= i <= index + |s| <= a.Length
    invariant a[..] == old(a[..index]) + s[..i - index] + old(a[i..])
  {
    label A:
    a[i] := s[i - index];
    calc {
      a[..];
    ==  // assignment statement above
      old@A(a[..])[i := s[i - index]];
    ==  // invariant on entry to loop
      (old(a[..index]) + s[..i - index] + old(a[i..]))[i := s[i - index]];
    ==  { assert old(a[..index]) + s[..i - index] + old(a[i..]) == (old(a[..index]) + s[..i - index]) + old(a[i..]); }
      ((old(a[..index]) + s[..i - index]) + old(a[i..]))[i := s[i - index]];
    ==  { assert |old(a[..index]) + s[..i - index]| == i; }
      (old(a[..index]) + s[..i - index]) + old(a[i..])[0 := s[i - index]];
    == { assert old(a[i..])[0 := s[i - index]] == [s[i - index]] + old(a[i..])[1..]; }
      (old(a[..index]) + s[..i - index]) + [s[i - index]] + old(a[i..])[1..];
    ==  { assert old(a[i..])[1..] == old(a[i + 1..]); }
      (old(a[..index]) + s[..i - index]) + [s[i - index]] + old(a[i + 1..]);
    ==  // redistribute +
      old(a[..index]) + (s[..i - index] + [s[i - index]]) + old(a[i + 1..]);
    ==  { assert s[..i - index] + [s[i - index]] == s[..i + 1 - index]; }
      old(a[..index]) + s[..i + 1 - index] + old(a[i + 1..]);
    }
    i := i + 1;
  }
}
