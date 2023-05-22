// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
   assert forall m :: (var m : multiset<int> := m; m) !! multiset{};

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
   requires 0 <= n < a.Length;
   modifies a;
   ensures multiset(a[..n+1]) == multiset(a[..n]) + multiset{e};
{
  a[n] := e;
  assert a[..n+1] == a[..n] + [e];
}
method test7(a: array<int>, i: int, j: int)
   requires 0 <= i < j < a.Length;
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
   requires 0 <= i < j < a.Length;
   modifies a;
   ensures old(multiset(a[..])) == multiset(a[..]);
   ensures a[j] == old (a[i]) && a[i] == old(a[j]);
   ensures forall k :: 0 <= k < a.Length && k !in {i, j} ==> a[k] == old(a[k]);
{
   a[i], a[j] := a[j], a[i];
}
method test9(a: array<int>, i: int, j: int, limit: int)
   requires 0 <= i < j < limit <= a.Length;
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
   requires 0 <= c < n <= a.Length;
   modifies a;
   ensures multiset(a[c..n-1]) == multiset(a[c..n]) - multiset{a[n-1]};
{
  assert a[c..n-1] + [a[n-1]] == a[c..n];
  assert multiset(a[c..n-1]) + multiset([a[n-1]]) == multiset(a[c..n]);
}
// ----------- the following tests mostly have to do with sets -------------

class BoxTests<G> {
  // ---------- sets ----------
  ghost method LemmaSet0<T>(a: set<T>, b: set<T>)
    requires forall x :: x in a ==> x in b;
    ensures a <= b;
  {
  }

  ghost method LemmaSet1(a: set<G>, b: set<G>)
    requires forall x :: x in a ==> x in b;
    ensures a <= b;
  {
  }

  ghost method LemmaSet2(a: set<int>, b: set<int>)
    requires forall x :: x in a ==> x in b;
    ensures a <= b;
  {
  }

  ghost method LemmaSet3(a: set<object>, b: set<object>)
    requires forall x :: x in a ==> x in b;
    ensures a <= b;
  {
  }

  ghost method LemmaSet4(a: set<bool>, b: set<bool>)
    requires forall x :: x in a ==> x in b;
    ensures a <= b;
  {
  }

  ghost method Lemma_NonEmpty(x : set<int>, y : set<int>)
    requires x * y == {};
    ensures x !! y;
  {
    assert forall k :: k !in (x*y);
  }

  // ---------- sequences (don't require any special tricks in the encoding) ----------
  ghost method LemmaSeq(a: seq<int>, b: seq<int>)
    requires |a| <= |b| && forall i :: 0 <= i < |a| ==> a[i] == b[i];
    ensures a <= b;
  {
  }

  // ---------- multisets ----------
  ghost method LemmaMultiset0<T>(a: multiset<T>, b: multiset<T>)
    requires forall x :: x in a ==> x in b;
    ensures a <= b;  // error: this property does not hold for multisets
  {
  }

  ghost method LemmaMultiset1(a: multiset<int>, b: multiset<int>)
    requires forall x :: x in a ==> x in b;
    ensures a <= b;  // error: this property does not hold for multisets
  {
  }
}

// ---------- indexing and updates ----------
method test12(a: nat, b: nat, c: int)
{
  var m0, m1, m2: multiset<bool>;
  m0 := multiset{false, true, true};
  m1 := multiset{true}[false := a];
  m2 := multiset{}[false := b];
  assert (m0 + m1 + m2)[true] == 3;
  assert (m1 * m2)[false] == if a <= b then a else b;
  m2 := m2[true := c]; // error: c might be negative
}


// ---------- cardinality ----------
method MultisetCardinalityA(s: multiset<int>)
  requires s != multiset{};
{
  if {
    case true =>  assert s != multiset{};
    case true =>  assert |s| != 0;
    case true =>  assert exists x :: x in s;
    case true =>  var y :| y in s;
  }
}

method MultisetCardinalityB(s: multiset<int>)
  requires |s| != 0;
{
  if {
    case true =>  assert s != multiset{};
    case true =>  assert |s| != 0;
    case true =>  assert exists x :: x in s;
    case true =>  var y :| y in s;
  }
}

method MultisetCardinalityC(s: multiset<int>)
  requires exists x :: x in s;
{
  if {
    case true =>  assert s != multiset{};
    case true =>  assert |s| != 0;
    case true =>  assert exists x :: x in s;
    case true =>  var y :| y in s;
  }
}

method MultisetCardinalityA'(s: multiset<int>)
  requires s == multiset{};
{
  if {
    case true =>  assert s == multiset{};
    case true =>  assert |s| == 0;
    case true =>  assert !exists x :: x in s;
    case true =>  var y :| y !in s;
  }
}

method MultisetCardinalityB'(s: multiset<int>)
  requires |s| == 0;
{
  if {
    case true =>  assert s == multiset{};
    case true =>  assert |s| == 0;
    case true =>  assert !exists x :: x in s;
    case true =>  var y :| y !in s;
  }
}

method MultisetCardinalityC'(s: multiset<int>)
  requires forall x :: x !in s;
{
  if {
    case true =>  assert s == multiset{};
    case true =>  assert |s| == 0;
    case true =>  assert !exists x :: x in s;
    case true =>  var y :| y !in s;
  }
}

method LetSuchThatExpression(s: multiset<int>)
  ensures |s| != 0 ==> var x :| x in s; true;
{
}

// ----------- things that at one point were axioms -------------

method MultiSetProperty0(s: multiset<object>, t: multiset<object>, p: object)
{
  if 0 < s[p] {
    assert 0 < (s + t)[p];
  }
  if 0 < t[p] {
    assert 0 < (s + t)[p];
  }
  if * {
    assert s + t - s == t;
  } else if * {
    assert s + t - t == s;
  } else {
    assert s + (t - s) == t;  // error
  }
}

// ---------- additional properties

lemma UpperBoundOnOccurrenceCount(s: multiset<int>, x: int)
  ensures 0 <= s[x] <= |s|;
{
}

lemma MultisetCardinalityFromSequenceLength(s: seq<int>)
  ensures |multiset(s)| == |s|;
{
}

lemma Set_and_Multiset_Cardinalities(x: int, y: int)
{
  if * {
    assert 1 <= |{x,y}| <= 2;
    if x != y {
      assert 2 <= |{x,y}|;
    } else {
      assert 2 <= |{x,y}|;  // error
    }
  } else {
    assert |multiset{x,y}| == 2;
  }
}

// AutoTriggers explicitly removed, as simplifications of set expressions such
// as x in {1,2} cause invalid terms to appear in the triggers
