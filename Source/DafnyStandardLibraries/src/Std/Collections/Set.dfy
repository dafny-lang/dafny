/*******************************************************************************
 *  Original Copyright under the following:
 *  Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University,
 *  ETH Zurich, and University of Washington
 *  SPDX-License-Identifier: BSD-2-Clause
 *
 *  Copyright (c) Microsoft Corporation
 *  SPDX-License-Identifier: MIT
 *
 *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/**
 This module defines useful properties and functions relating to the built-in `set` type.
 */
module Std.Collections.Set {

  import opened Functions
  import opened Relations

  /* If all elements in set x are in set y, x is a subset of y. */
  lemma LemmaSubset<T>(x: set<T>, y: set<T>)
    requires forall e {:trigger e in y} :: e in x ==> e in y
    ensures x <= y
  {
  }

  /* If x is a subset of y, then the size of x is less than or equal to the
  size of y. */
  lemma LemmaSubsetSize<T>(x: set<T>, y: set<T>)
    ensures x < y ==> |x| < |y|
    ensures x <= y ==> |x| <= |y|
  {
    if x != {} {
      var e :| e in x;
      LemmaSubsetSize(x - {e}, y - {e});
    }
  }

  /* If x is a subset of y and the size of x is equal to the size of y, x is
  equal to y. */
  lemma LemmaSubsetEquality<T>(x: set<T>, y: set<T>)
    requires x <= y
    requires |x| == |y|
    ensures x == y
    decreases x, y
  {
    if x == {} {
    } else {
      var e :| e in x;
      LemmaSubsetEquality(x - {e}, y - {e});
    }
  }

  /* A singleton set has a size of 1. */
  lemma LemmaSingletonSize<T>(x: set<T>, e: T)
    requires x == {e}
    ensures |x| == 1
  {
  }

  /* Elements in a singleton set are equal to each other. */
  lemma LemmaSingletonEquality<T>(x: set<T>, a: T, b: T)
    requires |x| == 1
    requires a in x
    requires b in x
    ensures a == b
  {
    if a != b {
      assert {a} < x;
      LemmaSubsetSize({a}, x);
      assert false;
    }
  }

  /* A singleton set has at least one element and any two elements are equal. */
  ghost predicate IsSingleton<T>(s: set<T>) {
    && (exists x :: x in s)
    && (forall x, y | x in s && y in s :: x == y)
  }

  /* A set has exactly one element, if and only if, it has at least one element and any two elements are equal. */
  lemma LemmaIsSingleton<T>(s: set<T>)
    ensures |s| == 1 <==> IsSingleton(s)
  {
    if |s| == 1 {
      forall x, y | x in s && y in s ensures x == y {
        LemmaSingletonEquality(s, x, y);
      }
    }
    if IsSingleton(s) {
      var x :| x in s;
      assert s == {x};
      assert |s| == 1;
    }
  }

  /* Non-deterministically extracts an element from a set that contains at least one element. */
  ghost function ExtractFromNonEmptySet<T>(s: set<T>): (x: T)
    requires |s| != 0
    ensures x in s
  {
    var x :| x in s;
    x
  }

  /* Deterministically extracts the unique element from a singleton set. In contrast to
     `ExtractFromNonEmptySet`, this implementation compiles, as the uniqueness of the element
     being picked can be proven. */
  function ExtractFromSingleton<T>(s: set<T>): (x: T)
    requires |s| == 1
    ensures s == {x}
  {
    LemmaIsSingleton(s);
    var x :| x in s;
    x
  }

  /* If an injective function is applied to each element of a set to construct
  another set, the two sets have the same size.  */
  lemma LemmaMapSize<X(!new), Y>(xs: set<X>, ys: set<Y>, f: X-->Y)
    requires forall x {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    requires forall x {:trigger f(x)} :: x in xs <==> f(x) in ys
    requires forall y {:trigger y in ys} :: y in ys ==> exists x :: x in xs && y == f(x)
    ensures |xs| == |ys|
  {
    if xs != {} {
      var x :| x in xs;
      var xs' := xs - {x};
      var ys' := ys - {f(x)};
      LemmaMapSize(xs', ys', f);
    }
  }

  /* Map an injective function to each element of a set. */
  opaque function Map<X(!new), Y>(f: X --> Y, xs: set<X>): (ys: set<Y>)
    reads f.reads
    requires forall x {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    ensures forall x {:trigger f(x)} :: x in xs <==> f(x) in ys
    ensures |xs| == |ys|
  {
    var ys := set x | x in xs :: f(x);
    LemmaMapSize(xs, ys, f);
    ys
  }

  /* If a set ys is constructed using elements of another set xs for which a
  function returns true, the size of ys is less than or equal to the size of
  xs. */
  lemma LemmaFilterSize<X>(xs: set<X>, ys: set<X>, f: X~>bool)
    requires forall x {:trigger f.requires(x)}{:trigger x in xs} :: x in xs ==> f.requires(x)
    requires forall y {:trigger f(y)}{:trigger y in xs} :: y in ys ==> y in xs && f(y)
    ensures |ys| <= |xs|
    decreases xs, ys
  {
    if ys != {} {
      var y :| y in ys;
      var xs' := xs - {y};
      var ys' := ys - {y};
      LemmaFilterSize(xs', ys', f);
    }
  }

  /* Construct a set using elements of another set for which a function returns
  true. */
  opaque function Filter<X(!new)>(f: X ~> bool, xs: set<X>): (ys: set<X>)
    reads set x, o | x in xs && o in f.reads(x) :: o
    requires forall x {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    ensures forall y {:trigger f(y)}{:trigger y in xs} :: y in ys <==> y in xs && f(y)
    ensures |ys| <= |xs|
  {
    var ys := set x | x in xs && f(x);
    LemmaFilterSize(xs, ys, f);
    ys
  }

  /* The size of a union of two sets is greater than or equal to the size of
  either individual set. */
  lemma LemmaUnionSize<X>(xs: set<X>, ys: set<X>)
    ensures |xs + ys| >= |xs|
    ensures |xs + ys| >= |ys|
  {
    if ys == {} {
    } else {
      var y :| y in ys;
      if y in xs {
        var xr := xs - {y};
        var yr := ys - {y};
        assert xr + yr == xs + ys - {y};
        LemmaUnionSize(xr, yr);
      } else {
        var yr := ys - {y};
        assert xs + yr == xs + ys - {y};
        LemmaUnionSize(xs, yr);
      }
    }
  }

  /* Construct a set with all integers in the range [a, b). */
  opaque function SetRange(a: int, b: int): (s: set<int>)
    requires a <= b
    ensures forall i {:trigger i in s} :: a <= i < b <==> i in s
    ensures |s| == b - a
    decreases b - a
  {
    if a == b then {} else {a} + SetRange(a + 1, b)
  }

  /* Construct a set with all integers in the range [0, n). */
  opaque function SetRangeZeroBound(n: int): (s: set<int>)
    requires n >= 0
    ensures forall i {:trigger i in s} :: 0 <= i < n <==> i in s
    ensures |s| == n
  {
    SetRange(0, n)
  }

  /* If a set solely contains integers in the range [a, b), then its size is
  bounded by b - a. */
  lemma LemmaBoundedSetSize(x: set<int>, a: int, b: int)
    requires forall i {:trigger i in x} :: i in x ==> a <= i < b
    requires a <= b
    ensures |x| <= b - a
  {
    var range := SetRange(a, b);
    forall e {:trigger e in range}{:trigger e in x} | e in x
      ensures e in range
    {
    }
    assert x <= range;
    LemmaSubsetSize(x, range);
  }

  /** In a set, a greatest element is necessarily maximal. */
  lemma LemmaGreatestImpliesMaximal<T(!new)>(R: (T, T) -> bool, max: T, s: set<T>)
    requires IsGreatest(R, max, s)
    ensures IsMaximal(R, max, s)
  {
  }

  /** In a set, a least element is necessarily minimal. */
  lemma LemmaLeastImpliesMinimal<T(!new)>(R: (T, T) -> bool, min: T, s: set<T>)
    requires IsLeast(R, min, s)
    ensures IsMinimal(R, min, s)
  {
  }

  /** In a totally-ordered set, an element is maximal if and only if it is a greatest element. */
  lemma LemmaMaximalEquivalentGreatest<T(!new)>(R: (T, T) -> bool, max: T, s: set<T>)
    requires TotalOrdering(R)
    ensures IsGreatest(R, max, s) <==> IsMaximal(R, max, s)
  {
  }

  /** In a totally-ordered set, an element is minimal if and only if it is a least element. */
  lemma LemmaMinimalEquivalentLeast<T(!new)>(R: (T, T) -> bool, min: T, s: set<T>)
    requires TotalOrdering(R)
    ensures IsLeast(R, min, s) <==> IsMinimal(R, min, s)
  {
  }

  /** In a partially-ordered set, there exists at most one least element. */
  lemma LemmaLeastIsUnique<T(!new)>(R: (T, T) -> bool, s: set<T>)
    requires PartialOrdering(R)
    ensures forall min, min' | IsLeast(R, min, s) && IsLeast(R, min', s) :: min == min'
  {}

  /** In a partially-ordered set, there exists at most one greatest element. */
  lemma LemmaGreatestIsUnique<T(!new)>(R: (T, T) -> bool, s: set<T>)
    requires PartialOrdering(R)
    ensures forall max, max' | IsGreatest(R, max, s) && IsGreatest(R, max', s) :: max == max'
  {}

  /** In a totally-ordered set, there exists at most one minimal element. */
  lemma LemmaMinimalIsUnique<T(!new)>(R: (T, T) -> bool, s: set<T>)
    requires TotalOrdering(R)
    ensures forall min, min' | IsMinimal(R, min, s) && IsMinimal(R, min', s) :: min == min'
  {}

  /** In a totally-ordered set, there exists at most one maximal element. */
  lemma LemmaMaximalIsUnique<T(!new)>(R: (T, T) -> bool, s: set<T>)
    requires TotalOrdering(R)
    ensures forall max, max' | IsMaximal(R, max, s) && IsMaximal(R, max', s) :: max == max'
  {}

  /** Any totally-ordered set contains a unique minimal (equivalently, least) element. */
  lemma LemmaFindUniqueMinimal<T(!new)>(R: (T, T) -> bool, s: set<T>) returns (min: T)
    requires |s| > 0 && TotalOrdering(R)
    ensures IsMinimal(R, min, s) && (forall min': T | IsMinimal(R, min', s) :: min == min')
  {
    var x :| x in s;
    if s == {x} {
      min := x;
    } else {
      var min' := LemmaFindUniqueMinimal(R, s - {x});
      if
      case R(min', x) => min := min';
      case R(x, min') => min := x;
    }
  }

  /** Any totally ordered set contains a unique maximal (equivalently, greatest) element. */
  lemma LemmaFindUniqueMaximal<T(!new)>(R: (T, T) -> bool, s: set<T>) returns (max: T)
    requires |s| > 0 && TotalOrdering(R)
    ensures IsMaximal(R, max, s) && (forall max': T | IsMaximal(R, max', s) :: max == max')
  {
    var x :| x in s;
    if s == {x} {
      max := x;
    } else {
      var max' := LemmaFindUniqueMaximal(R, s - {x});
      if
      case R(max', x) => max := x;
      case R(x, max') => max := max';
    }
  }
}
