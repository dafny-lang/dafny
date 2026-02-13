/*******************************************************************************
 *  Original: Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University,
 *  ETH Zurich, and University of Washington
 *  SPDX-License-Identifier: BSD-2-Clause
 *
 *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/**
 This module defines useful properties and functions relating to the built-in `map` type.
 */
module Std.Collections.Map {

  import opened Wrappers

  function Get<X, Y>(m: map<X, Y>, x: X): Option<Y>
  {
    if x in m then Some(m[x]) else None
  }

  function ToImap<X, Y>(m: map<X, Y>): (m': imap<X, Y>)
    ensures forall x {:trigger m'[x]} :: x in m ==> x in m' && m'[x] == m[x]
    ensures forall x {:trigger x in m'} :: x in m' ==> x in m
  {
    imap x | x in m :: m[x]
  }

  /* Remove all key-value pairs corresponding to the set of keys provided. */
  function RemoveKeys<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures forall x {:trigger m'[x]} :: x in m && x !in xs ==> x in m' && m'[x] == m[x]
    ensures forall x {:trigger x in m'} :: x in m' ==> x in m && x !in xs
    ensures m'.Keys == m.Keys - xs
  {
    m - xs
  }

  /* Remove a key-value pair. Returns unmodified map if key is not found. */
  function Remove<X, Y>(m: map<X, Y>, x: X): (m': map<X, Y>)
    ensures m' == RemoveKeys(m, {x})
    ensures |m'.Keys| <= |m.Keys|
    ensures x in m ==> |m'| == |m| - 1
    ensures x !in m ==> |m'| == |m|
  {
    var m' := map x' | x' in m && x' != x :: m[x'];
    assert m'.Keys == m.Keys - {x};
    m'
  }

  /* Keep all key-value pairs corresponding to the set of keys provided. */
  function Restrict<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures m' == RemoveKeys(m, m.Keys - xs)
  {
    map x | x in xs && x in m :: m[x]
  }

  /* True iff x maps to the same value or does not exist in m and m'. */
  ghost predicate EqualOnKey<X, Y>(m: map<X, Y>, m': map<X, Y>, x: X)
  {
    (x !in m && x !in m') || (x in m && x in m' && m[x] == m'[x])
  }

  /* True iff m is a subset of m'. */
  ghost predicate IsSubset<X, Y>(m: map<X, Y>, m': map<X, Y>)
  {
    && m.Keys <= m'.Keys
    && forall x {:trigger EqualOnKey(m, m', x)}{:trigger x in m} :: x in m ==> EqualOnKey(m, m', x)
  }

  /* Union of two maps. Does not require disjoint domains; on the intersection,
  values from the second map are chosen. */
  function Union<X, Y>(m: map<X, Y>, m': map<X, Y>): (r: map<X, Y>)
    ensures r.Keys == m.Keys + m'.Keys
    ensures forall x {:trigger r[x]} :: x in m' ==> r[x] == m'[x]
    ensures forall x {:trigger r[x]} :: x in m && x !in m' ==> r[x] == m[x]
  {
    m + m'
  }

  /* The size of the disjoint union is equal to the sum of individual map
  sizes. */
  lemma LemmaDisjointUnionSize<X, Y>(m: map<X, Y>, m': map<X, Y>)
    requires m.Keys !! m'.Keys
    ensures |Union(m, m')| == |m| + |m'|
  {
    var u := Union(m, m');
    assert |u.Keys| == |m.Keys| + |m'.Keys|;
  }

  /* True iff a map is injective. */
  ghost predicate Injective<X, Y>(m: map<X, Y>)
  {
    forall x, x' {:trigger m[x], m[x']} :: x != x' && x in m && x' in m ==> m[x] != m[x']
  }

  /* Swaps map keys and values. Values are not required to be unique; no
  promises on which key is chosen on the intersection. */
  ghost function Invert<X, Y>(m: map<X, Y>): map<Y, X>
  {
    map y | y in m.Values :: var x :| x in m.Keys && m[x] == y; x
  }

  /* Inverted maps are injective. */
  lemma LemmaInvertIsInjective<X, Y>(m: map<X, Y>)
    ensures Injective(Invert(m))
  {
  }

  /* True iff a map contains all valid keys. */
  ghost predicate Total<X(!new), Y>(m: map<X, Y>)
  {
    forall i {:trigger m[i]}{:trigger i in m} :: i in m
  }

  /* True iff a map is monotonic. */
  ghost predicate Monotonic(m: map<int, int>)
  {
    forall x, x' {:trigger m[x], m[x']} :: x in m && x' in m && x <= x' ==> m[x] <= m[x']
  }

  /* True iff a map is monotonic. Only considers keys greater than or
  equal to start. */
  ghost predicate MonotonicFrom(m: map<int, int>, start: int)
  {
    forall x, x' {:trigger m[x], m[x']} :: x in m && x' in m && start <= x <= x' ==> m[x] <= m[x']
  }

}
