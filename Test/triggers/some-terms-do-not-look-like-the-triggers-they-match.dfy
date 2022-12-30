// RUN: %exits-with 4 %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file shows how Dafny detects loops even for terms that are not literal
// AST matches. This file also checks that triggers are reported exactly as
// picked (that is, `x in s` yields `s[x]` for a multiset s), but matches as
// they appear in the buffer text (that is, `x+1 in s` is not translated to
// s[x+1] when highlighted as a cause for a potential matching loop.

method M() {
  // This is an obvious loop
  ghost var b := forall s: multiset<int>, x: int :: s[x] > 0 ==> s[x+1] > 0;

  // x in s loops with s[x+1] due to the way [x in s] is translated
  ghost var a := forall s: multiset<int>, x: int :: x in s ==> s[x+1] > 0 && x+2 !in s;
}

// "in" expressions are often rewritten by the ExpressionTranslator. The following
// tests check that triggers are not selected from expressions that will be
// rewritten.

method RewriteSet(s: set<int>, t: set<int>) {
  // set union
  ghost var u0 := forall x | x in s + t :: x < 200;
  ghost var u1 := forall x | x in s || x in t :: x < 200;
  ghost var u2 := set x | x in s + t;
  ghost var u3 := set x | x in s + t && (x in s || x in t);
  assert u0 == u1 && u2 == u3;

  // set intersection
  ghost var i0 := forall x | x in s * t :: x < 200;
  ghost var i1 := forall x | x in s * t && x in s && x in t :: x < 200;
  assert i0 == i1;

  // set difference
  ghost var d0 := forall x | x in s - t :: x < 200;
  ghost var d1 := forall x | x in s - t && x in s && x !in t :: x < 200;
  assert d0 == d1;

  // set display
  if * {
    // bad, since these quantifiers have no triggers
    ghost var c0 := forall x | x in {2, 3, 5} :: x < 200; // warning: no trigger
    ghost var c1 := forall x | x in ({2, 3, 5}) :: x < 200; // warning: no trigger
    assert c0 == c1;
  } else {
    // good
    var s := {2, 3, 5};
    ghost var c0 := forall x | x in s :: x < 200;
    ghost var c1 := forall x | x in (s) :: x < 200;
    assert c0 == c1;
  }

  // set comprehension
  ghost var h0 := forall x :: (x in set y | y in s) ==> x < 200; // warning: no trigger
  ghost var h1 := forall x :: var S := set y | y in s; x in S ==> x < 200; // warning: no trigger
  assert h0 == h1;
  ghost var h2 := forall x :: var S := F(set y | y in s); x in S ==> x < 200; // warning: no trigger
  ghost var h3 := forall x :: x in s ==> x < 200;
  ghost var h4 := forall x :: x in F(s) ==> x < 200;
}

function F<X>(s: X): X { s }

method RewriteMultiSet(s: multiset<int>, t: multiset<int>) {
  // multiset union
  ghost var u0 := forall x | x in s + t :: x < 200;
  ghost var u1 := forall x | x in s || x in t :: x < 200;
  assert u0 == u1 by {
    // here's one way to prove it
    assert forall x :: x in s + t <==> x in s || x in t;
  }

  // multiset intersection
  ghost var i0 := forall x | x in s * t :: x < 200;
  ghost var i1 := forall x | x in s && x in t :: x < 200;
  assert i0 == i1 by {
    // here's a different way to prove this one
    assert i0 == forall x | x in s * t && x in s && x in t :: x < 200;
  }

  // multiset difference
  ghost var d0 := forall x | x in s - t :: x < 200; // fine (multiset difference is not rewritten)
  ghost var d1 := forall x | x in s && s[x] > t[x] :: x < 200;
  assert d0 == d1 by {
    assert forall x :: x in s - t <==> x in s && s[x] > t[x];
  }

  // multiset display
  if * {
    // bad, since these quantifiers have no triggers
    ghost var c0 := forall x | x in multiset{2, 3, 5} :: x < 200; // warning: no trigger
    ghost var c1 := forall x | x in (multiset{2, 3, 5}) :: x < 200; // warning: no trigger
    assert c0 == c1;
  } else {
    // good
    var ms := multiset{2, 3, 5};
    ghost var c0 := forall x | x in ms :: x < 200;
    ghost var c1 := forall x | x in (ms) :: x < 200;
    assert c0 == c1;
  }
}

method RewriteSeq(s: seq<int>, t: seq<int>) {
  // concat
  ghost var u0 := forall x | x in s + t :: x < 200; // fine (seq + does is not rewritten)
  ghost var u1 := forall x | x in s || x in t :: x < 200;
  assert u0 == u1 by {
    if u0 {
      forall x | x in s || x in t
        ensures x < 200
      {
        assert x in s + t;
      }
      assert u1;
    }
    assert u1 ==> u0;
  }

  // seq display
  ghost var c0 := forall x | x in [2, 3, 5] :: x < 200; // fine (currently, "in seq-display" is not rewritten)
  ghost var c1 := forall x | x in ([2, 3, 5]) :: x < 200;
  assert c0 == c1;
}

method RewriteMap(s: map<int, int>, t: map<int, int>, u: set<int>) {
  // map merge
  ghost var u0 := forall x | x in s + t :: x < 200; // fine (map merge is not rewritten)
  ghost var u1 := forall x | x in s || x in t :: x < 200;
  assert u0 == u1;

  // map domain subtraction
  ghost var d0 := forall x | x in s - u :: x < 200; // fine (map subtraction is not rewritten)
  ghost var d1 := forall x | x in s && x !in u :: x < 200;
  assert d0 == d1 by {
    if d0 {
      forall x | x in s && x !in u
        ensures x < 200
      {
        assert x in s - u;
      }
      assert d1;
    }
    assert d1 ==> d0;
  }

  // map display
  ghost var c0 := forall x | x in map[2 := 20, 3 := 30, 5 := 50] :: x < 200; // fine (map comprehension is not rewritten)
  ghost var c1 := forall x | x in F(map[2 := 20, 3 := 30, 5 := 50]) :: x < 200;
  assert c0 == c1;

  assert false;  // error: sanity check
}

method Orderings(s: set<int>, ms: multiset<int>, q: seq<int>) {
  var a0 := exists x :: x < s; // trigger: x <= s
  var a1 := exists x :: x <= s;
  var a2 := exists x :: x >= s;
  var a3 := exists x :: x > s; // trigger: x >= s

  var b0 := exists x :: x < ms; // trigger: x <= ms
  var b1 := exists x :: x <= ms;
  var b2 := exists x :: x >= ms;
  var b3 := exists x :: x > ms; // trigger: x >= ms

  var c0 := exists x :: x < q; // warning: no trigger
  var c1 := exists x :: x <= q; // warning: no trigger
  assert true; // make sure all this gets sent to Boogie
}
