
method test1()
{
   var ms: multiset<int> := multiset{1,1,1};
   var ms2: multiset<int> := multiset{3};
   assert 1 in ms;
   assert forall i :: i != 1 ==> i !in ms; // 1 is the only thing in ms.
   
   assert ((ms - multiset{1}) - multiset {1}) != multiset{}; // it has more than 2 ones
   assert ((ms - multiset{1}) - multiset {1}) - multiset{1} == multiset{}; // and exactly three

   assert ms2 - ms == ms2; // set difference works correctly.
   assert ms - multiset{1} == multiset{1,1};
   assert !(multiset{1} !! multiset{1});
   assert exists m :: !(m !! multiset{1});
   assert forall m :: m !! multiset{};

   assert forall s :: (s == set x: int | x in ms :: x) ==> s == {1};
}

method test2(ms: multiset<int>)
{
   var s := set x | x in ms :: x; // seems to be a reasonable conversion
   assert forall x :: x in s <==> x in ms;
   assert ms !! multiset{};
}

method test3(s: set<int>)
{
   assert forall x :: x in s <==> x in multiset(s);
}
method test4(sq: seq<int>, a: array<int>)
   requires a != null;
   modifies a;
{
   assert sq == sq[..|sq|];
   assert sq == sq[0..];
   assert sq == sq[..];

   assert a.Length >= 0;
   var s := a[..];
}

method test5()
{
   assert multiset({1,1}) == multiset{1};
   assert multiset([1,1]) == multiset{1,1};
}

method test6(a: array<int>, n: int, e: int)
   requires a != null && 0 <= n < a.Length;
   modifies a;
   ensures multiset(a[..n+1]) == multiset(a[..n]) + multiset{e};
{
  a[n] := e;
  assert a[..n+1] == a[..n] + [e];
}
method test7(a: array<int>, i: int, j: int)
   requires a != null && 0 <= i < j < a.Length;
   modifies a;
   ensures old(multiset(a[..])) == multiset(a[..]);
   ensures a[j] == old (a[i]) && a[i] == old(a[j]);
   ensures forall k :: 0 <= k < a.Length && k !in {i, j} ==> a[k] == old(a[k]);
{
   ghost var s := a[..i] + [a[i]] + a[i+1 .. j] + [a[j]] + a[j+1..];
   assert a[..] == s;
   a[i], a[j] := a[j], a[i];
   assert a[..] == a[..i] + [a[i]] + a[i+1 .. j] + [a[j]] + a[j+1..];
   assert s == a[..i] + [old(a[i])] + a[i+1 .. j] + [old(a[j])] + a[j+1..];
}
method test8(a: array<int>, i: int, j: int)
   requires a != null && 0 <= i < j < a.Length;
   modifies a;
   ensures old(multiset(a[..])) == multiset(a[..]);
   ensures a[j] == old (a[i]) && a[i] == old(a[j]);
   ensures forall k :: 0 <= k < a.Length && k !in {i, j} ==> a[k] == old(a[k]);
{
   a[i], a[j] := a[j], a[i];
}
method test9(a: array<int>, i: int, j: int, limit: int)
   requires a != null && 0 <= i < j < limit <= a.Length;
   modifies a;
   ensures multiset(a[0..limit]) == old(multiset(a[0..limit]));
   ensures a[j] == old (a[i]) && a[i] == old(a[j]);
   ensures forall k :: 0 <= k < limit && k !in {i, j} ==> a[k] == old(a[k]);
{
   a[i], a[j] := a[j], a[i];
}
method test10(s: seq<int>)
   requires |s| > 4;
{
   assert multiset( s[3 := 2] ) == multiset(s) - multiset{s[3]} + multiset{2};
   assert multiset( (s[2 := 1])[3 := 2] ) == (((multiset(s) - multiset{s[2]}) + multiset{1})  - multiset{s[3]}) + multiset{2};
   assert multiset( (s[2 := s[3]])[3 := s[2]] ) == (((multiset(s) - multiset{s[2]}) + multiset{s[3]})  - multiset{s[3]}) + multiset{s[2]};
}

method test11(a: array<int>, n: int, c: int)
   requires a != null && 0 <= c < n <= a.Length;
   modifies a;
   ensures multiset(a[c..n-1]) == multiset(a[c..n]) - multiset{a[n-1]};
{

}