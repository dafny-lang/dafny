// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The following compiled function was always handled correctly:

function PickOne0(s: set<int>): int
  requires s != {}
{
  var u :| u in s;  // error: u is not picked uniquely
  u
}

// In PickOne1 and PickOne2, the body of the outer let expression
// wasn't checked properly for compile restrictions. In other words, the
// outer let expression had masked any such errors in its body.

function PickOne1(s: set<int>): int
  requires s != {}
{
  var w := 10;
  var u :| u in s;  // error: u is not picked uniquely
  u
}

function PickOne2(s: set<int>): int
  requires s != {}
{
  var w :| w == 10;
  var u :| u in s;  // error: u is not picked uniquely
  u
}

// Here are the two larger examples given in the bug report:

module M0 {
  ghost predicate setIsSeq<T>(t: set<T>, q: seq<T>) {
    |t| == |q| ==>
      (forall i :: 0 <= i < |q| ==> q[i] in t) &&
      (forall x :: x in t ==> x in q)
  }

  function fSetToSeq<T>(t: set<T>): (r: seq<T>)
    ensures setIsSeq(t, r)
  {
    var inner := t;
    if |inner| == 0 then
      []
    else
      var e :| e in inner;  // error: e is not picked uniquely
      var tx := inner - {e};
      var qx := fSetToSeq(tx);
      [e] + qx
  }

  lemma whatIsSeq<T>(s1: set<T>, s2: set<T>)
    ensures s1 == s2 ==> fSetToSeq(s1) == fSetToSeq(s2)
  {}

  method Test() {
    var s := {1, 2, 3};
    var t := {3, 1, 2};
    assert s == t;

    var a := fSetToSeq(s);
    var b := fSetToSeq(t);
    assert a == b;
    print "a = ", a, "  ==  b = ", b, "  ??  \n";

    var c := [1, 2, 3];
    var d := [3, 1, 2];
    assert c != d;
    print "c = ", c, "  !=  d = ", d, "  ??  \n";
  }
}

module M1 {
  ghost predicate setIsSeq(t: set, q: seq) {
    |t| == |q| ==>
      (forall i :: 0 <= i < |q| ==> q[i] in t) &&
      (forall x :: x in t ==> x in q)
  }

  function fSetToSeq(t: set): (r: seq)
    ensures setIsSeq(t, r)
   {
    var notUsed := t;
    if |t| == 0 then
      []
    else
      var e :| e in t;  // error: e is not picked uniquely
      var tx := t - {e};
      var qx := fSetToSeq(tx);
      [e] + qx
  }
}
