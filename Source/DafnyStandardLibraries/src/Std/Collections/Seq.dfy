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
 This module defines useful properties and functions relating to the built-in `seq` type.
 */
module Std.Collections.Seq {

  import opened Wrappers
  import opened Relations
  import Math

  /**********************************************************
   *
   *  Manipulating the End of a Sequence
   *
   ***********************************************************/

  /* Returns the first element of a non-empty sequence. */
  function First<T>(xs: seq<T>): T
    requires |xs| > 0
  {
    xs[0]
  }

  /* Returns the subsequence of a non-empty sequence obtained by
     dropping the first element. */
  function DropFirst<T>(xs: seq<T>): seq<T>
    requires |xs| > 0
  {
    xs[1..]
  }

  /* Returns the last element of a non-empty sequence. */
  function Last<T>(xs: seq<T>): T
    requires |xs| > 0
  {
    xs[|xs|-1]
  }

  /* Returns the subsequence of a non-empty sequence obtained by
     dropping the last element. */
  function DropLast<T>(xs: seq<T>): seq<T>
    requires |xs| > 0
  {
    xs[..|xs|-1]
  }

  lemma TakeLess<T>(s: seq<T>, m: nat, n: nat)
    requires m <= n <= |s|
    ensures s[..n][..m] == s[..m]
  {
  }

  /* The concatenation of two subsequences of a non-empty sequence, the first obtained
     from dropping the last element, the second consisting only of the last
     element, is the original sequence. */
  lemma LemmaLast<T>(xs: seq<T>)
    requires |xs| > 0
    ensures DropLast(xs) + [Last(xs)] == xs
  {
  }

  /* The last element of two concatenated sequences, the second one being non-empty, will be the
     last element of the latter sequence. */
  lemma LemmaAppendLast<T>(xs: seq<T>, ys: seq<T>)
    requires 0 < |ys|
    ensures Last(xs + ys) == Last(ys)
  {
  }

  /* The concatenation of sequences is associative (three arguments). */
  lemma LemmaConcatIsAssociative<T>(xs: seq<T>, ys: seq<T>, zs: seq<T>)
    ensures xs + (ys + zs) == xs + ys + zs == (xs + ys) + zs
  {
  }

  /* The concatenation of sequences is associative (four arguments). */
  lemma LemmaConcatIsAssociative2<T>(a: seq<T>, b: seq<T>, c: seq<T>, d: seq<T>)
    ensures a + b + c + d == a + (b + c + d)
  {
  }

  /* The empty sequence is the right identity of the concatenation operation. */
  lemma EmptySequenceIsRightIdentity(l: seq)
    ensures l == l + []
  {}

  /**********************************************************
   *
   *  Manipulating the Content of a Sequence
   *
   ***********************************************************/

  /* Is true if the sequence xs is a prefix of the sequence ys. */
  ghost predicate IsPrefix<T>(xs: seq<T>, ys: seq<T>)
    ensures IsPrefix(xs, ys) ==> (|xs| <= |ys| && xs == ys[..|xs|])
  {
    xs <= ys
  }

  /* Is true if the sequence xs is a suffix of the sequence ys. */
  ghost predicate IsSuffix<T>(xs: seq<T>, ys: seq<T>)
  {
    && |xs| <= |ys|
    && xs == ys[|ys|-|xs|..]
  }

  /* A sequence that is sliced at the pos-th element, concatenated
     with that same sequence sliced from the pos-th element, is equal to the
     original unsliced sequence. */
  lemma LemmaSplitAt<T>(xs: seq<T>, pos: nat)
    requires pos < |xs|
    ensures xs[..pos] + xs[pos..] == xs
  {
  }

  /* Any element in a slice is included in the original sequence. */
  lemma LemmaElementFromSlice<T>(xs: seq<T>, xs': seq<T>, a: int, b: int, pos: nat)
    requires 0 <= a <= pos < b <= |xs|
    requires xs' == xs[a..b]
    ensures  pos - a < |xs'|
    ensures  xs'[pos-a] == xs[pos]
  {
  }

  /* A slice (from s2..e2) of a slice (from s1..e1) of a sequence is equal to just a
     slice (s1+s2..s1+e2) of the original sequence. */
  lemma LemmaSliceOfSlice<T>(xs: seq<T>, s1: int, e1: int, s2: int, e2: int)
    requires 0 <= s1 <= e1 <= |xs|
    requires 0 <= s2 <= e2 <= e1 - s1
    ensures  xs[s1..e1][s2..e2] == xs[s1+s2..s1+e2]
  {
    var r1 := xs[s1..e1];
    var r2 := r1[s2..e2];
    var r3 := xs[s1+s2..s1+e2];
    assert |r2| == |r3|;
    forall i {:trigger r2[i], r3[i]}| 0 <= i < |r2| ensures r2[i] == r3[i]
    {
    }
  }

  /* Converts a sequence to an array. */
  method ToArray<T>(xs: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |xs|
    ensures forall i :: 0 <= i < |xs| ==> a[i] == xs[i]
  {
    a := new T[|xs|](i requires 0 <= i < |xs| => xs[i]);
  }

  /* Converts a sequence to a set. */
  function ToSet<T>(xs: seq<T>): set<T>
  {
    set x: T | x in xs
  }

  /* The cardinality of a set of elements is always less than or
     equal to that of the full sequence of elements. */
  lemma LemmaCardinalityOfSet<T>(xs: seq<T>)
    ensures |ToSet(xs)| <= |xs|
  {
    if |xs| == 0 {
    } else {
      assert ToSet(xs) == ToSet(DropLast(xs)) + {Last(xs)};
      LemmaCardinalityOfSet(DropLast(xs));
    }
  }

  /* A sequence is of length 0 if and only if its conversion to
     a set results in the empty set. */
  lemma LemmaCardinalityOfEmptySetIs0<T>(xs: seq<T>)
    ensures |ToSet(xs)| == 0 <==> |xs| == 0
  {
    if |xs| != 0 {
      assert xs[0] in ToSet(xs);
    }
  }

  /* Is true if there are no duplicate values in the sequence. */
  ghost predicate HasNoDuplicates<T>(xs: seq<T>)
  {
    forall i, j :: 0 <= i < |xs| && 0 <= j < |xs| && i != j ==> xs[i] != xs[j]
  }

  /* If sequences xs and ys don't have duplicates and there are no
     elements in common between them, then the concatenated sequence xs + ys
     will not contain duplicates either. */
  @TimeLimitMultiplier(3)
  lemma LemmaNoDuplicatesInConcat<T>(xs: seq<T>, ys: seq<T>)
    requires HasNoDuplicates(xs)
    requires HasNoDuplicates(ys)
    requires multiset(xs) !! multiset(ys)
    ensures HasNoDuplicates(xs+ys)
  {
    var zs := xs + ys;
    if |zs| > 1 {
      assert forall i :: 0 <= i < |xs| ==> zs[i] in multiset(xs);
      assert forall j :: |xs| <= j < |zs| ==> zs[j] in multiset(ys);
      assert forall i, j :: 0 <= i < |xs| <= j < |zs| ==> zs[i] != zs[j];
    }
  }

  /* The inverse of LemmaNoDuplicatesInConcat:
     If the concatenated sequence xs + ys doesn't have duplicates,
     then xs and ys don't either and are disjoint. */
  lemma LemmaNoDuplicatesDecomposition<T>(xs: seq<T>, ys: seq<T>)
    requires HasNoDuplicates(xs+ys)
    ensures HasNoDuplicates(xs)
    ensures HasNoDuplicates(ys)
    ensures multiset(xs) !! multiset(ys)
  {
    var zs := xs + ys;
    if !HasNoDuplicates(xs) {
      assert false by {
        var i, j :| 0 <= i < j < |xs| && xs[i] == xs[j];
        assert zs[i] == zs[j];
        assert !HasNoDuplicates(zs);
      }
    }
    if !HasNoDuplicates(ys) {
      assert false by {
        var i, j :| 0 <= i < j < |ys| && ys[i] == ys[j];
        assert zs[|xs| + i] == zs[|xs| + j];
        assert !HasNoDuplicates(zs);
      }
    }
    if !(multiset(xs) !! multiset(ys)) {
      assert false by {
        var i, j :| 0 <= i < |xs| && 0 <= j < |ys| && xs[i] == ys[j];
        assert zs[i] == zs[|xs| + j];
        assert !HasNoDuplicates(zs);
      }
    }
  }

  /* A sequence with no duplicates converts to a set of the same
     cardinality. */
  lemma LemmaCardinalityOfSetNoDuplicates<T>(xs: seq<T>)
    requires HasNoDuplicates(xs)
    ensures |ToSet(xs)| == |xs|
  {
    if |xs| == 0 {
    } else {
      LemmaCardinalityOfSetNoDuplicates(DropLast(xs));
      assert ToSet(xs) == ToSet(DropLast(xs)) + {Last(xs)};
    }
  }

  /* A sequence with cardinality equal to its set has no duplicates. */
  lemma LemmaNoDuplicatesCardinalityOfSet<T>(xs: seq<T>)
    requires |ToSet(xs)| == |xs|
    ensures HasNoDuplicates(xs)
  {
    if |xs| == 0 {
    } else {
      assert xs == [First(xs)] + DropFirst(xs);
      assert ToSet(xs) == {First(xs)} + ToSet(DropFirst(xs));
      if First(xs) in DropFirst(xs) {
        // If there is a duplicate, then we show that |ToSet(s)| == |s| cannot hold.
        assert ToSet(xs) == ToSet(DropFirst(xs));
        LemmaCardinalityOfSet(DropFirst(xs));
      } else {
        assert |ToSet(xs)| == 1 + |ToSet(DropFirst(xs))|;
        LemmaNoDuplicatesCardinalityOfSet(DropFirst(xs));
      }
    }
  }

  /* Given a sequence with no duplicates, each element occurs only
     once in its conversion to a multiset. */
  lemma LemmaMultisetHasNoDuplicates<T>(xs: seq<T>)
    requires HasNoDuplicates(xs)
    ensures forall x {:trigger multiset(xs)[x]} | x in multiset(xs):: multiset(xs)[x] == 1
  {
    if |xs| == 0 {
    } else {
      assert xs == DropLast(xs) + [Last(xs)];
      assert Last(xs) !in DropLast(xs) by {
      }
      assert HasNoDuplicates(DropLast(xs)) by {
      }
      LemmaMultisetHasNoDuplicates(DropLast(xs));
    }
  }

  /* For an element that occurs at least once in a sequence, the index of its
     first occurrence is returned. */
  opaque function IndexOf<T(==)>(xs: seq<T>, v: T): (i: nat)
    requires v in xs
    ensures i < |xs| && xs[i] == v
    ensures forall j :: 0 <= j < i ==> xs[j] != v
  {
    if xs[0] == v then 0 else 1 + IndexOf(xs[1..], v)
  }

  /* Returns Some(i), if an element occurs at least once in a sequence, and i is
     the index of its first occurrence. Otherwise the return is None. */
  opaque function IndexOfOption<T(==)>(xs: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |xs| && xs[o.value] == v &&
                            forall j :: 0 <= j < o.value ==> xs[j] != v
            else v !in xs
  {
    IndexByOption(xs, x => x == v)
  }

  /* Returns Some(i), if an element satisfying p occurs at least once in a sequence, and i is
    the index of the first such occurrence. Otherwise the return is None. */
  opaque function IndexByOption<T(==)>(xs: seq<T>, p: T -> bool): (o: Option<nat>)
    ensures if o.Some? then o.value < |xs| && p(xs[o.value]) &&
                            forall j :: 0 <= j < o.value ==> !p(xs[j])
            else forall x <- xs ::!p(x)
  {
    if |xs| == 0 then None()
    else
    if p(xs[0]) then Some(0)
    else
      var o' := IndexByOption(xs[1..], p);
      if o'.Some? then Some(o'.value + 1) else None()
  }

  /* For an element that occurs at least once in a sequence, the index of its
     last occurrence is returned. */
  opaque function LastIndexOf<T(==)>(xs: seq<T>, v: T): (i: nat)
    requires v in xs
    ensures i < |xs| && xs[i] == v
    ensures forall j :: i < j < |xs| ==> xs[j] != v
  {
    if xs[|xs|-1] == v then |xs| - 1 else LastIndexOf(xs[..|xs|-1], v)
  }

  /* Returns Some(i), if an element occurs at least once in a sequence, and i is
     the index of its last occurrence. Otherwise the return is None. */
  opaque function LastIndexOfOption<T(==)>(xs: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |xs| && xs[o.value] == v &&
                            forall j :: o.value < j < |xs| ==> xs[j] != v
            else v !in xs
  {
    LastIndexByOption(xs, x => x == v)
  }

  /* Returns Some(i), if an element satisfying p occurs at least once in a sequence, and i is
     the index of the last such occurrence. Otherwise the return is None. */
  opaque function LastIndexByOption<T(==)>(xs: seq<T>, p: T -> bool): (o: Option<nat>)
    ensures if o.Some? then o.value < |xs| && p(xs[o.value]) &&
                            forall j {:trigger xs[j]} :: o.value < j < |xs| ==> !p(xs[j])
            else forall x <- xs ::!p(x)
  {
    if |xs| == 0 then None()
    else if p(xs[|xs|-1]) then Some(|xs| - 1) else LastIndexByOption(xs[..|xs|-1], p)
  }

  /* Returns a sequence without the element at a given position. */
  opaque function Remove<T>(xs: seq<T>, pos: nat): (ys: seq<T>)
    requires pos < |xs|
    ensures |ys| == |xs| - 1
    ensures forall i {:trigger ys[i], xs[i]} | 0 <= i < pos :: ys[i] == xs[i]
    ensures forall i {:trigger ys[i]} | pos <= i < |xs| - 1 :: ys[i] == xs[i+1]
  {
    xs[..pos] + xs[pos+1..]
  }

  /* If a given element occurs at least once in a sequence, the sequence without
     its first occurrence is returned. Otherwise the same sequence is returned. */
  opaque function RemoveValue<T(==)>(xs: seq<T>, v: T): (ys: seq<T>)
    ensures v !in xs ==> xs == ys
    ensures v in xs ==> |multiset(ys)| == |multiset(xs)| - 1
    ensures v in xs ==> multiset(ys)[v] == multiset(xs)[v] - 1
    ensures HasNoDuplicates(xs) ==> HasNoDuplicates(ys) && ToSet(ys) == ToSet(xs) - {v}
  {
    if v !in xs then xs
    else
      var i := IndexOf(xs, v);
      assert xs == xs[..i] + [v] + xs[i+1..];
      xs[..i] + xs[i+1..]
  }

  /* Inserts an element at a given position and returns the resulting (longer) sequence. */
  opaque function Insert<T>(xs: seq<T>, a: T, pos: nat): seq<T>
    requires pos <= |xs|
    ensures |Insert(xs, a, pos)| == |xs| + 1
    ensures forall i {:trigger Insert(xs, a, pos)[i], xs[i]} :: 0 <= i < pos ==> Insert(xs, a, pos)[i] == xs[i]
    ensures forall i {:trigger xs[i]} :: pos <= i < |xs| ==> Insert(xs, a, pos)[i+1] == xs[i]
    ensures Insert(xs, a, pos)[pos] == a
    ensures multiset(Insert(xs, a, pos)) == multiset(xs) + multiset{a}
  {
    assert xs == xs[..pos] + xs[pos..];
    xs[..pos] + [a] + xs[pos..]
  }

  /* Returns the sequence that is in reverse order to a given sequence. */
  opaque function Reverse<T>(xs: seq<T>): (ys: seq<T>)
    ensures |ys| == |xs|
    ensures forall i {:trigger ys[i]}{:trigger xs[|xs| - i - 1]} :: 0 <= i < |xs| ==> ys[i] == xs[|xs| - i - 1]
  {
    if xs == [] then [] else [xs[|xs|-1]] + Reverse(xs[0 .. |xs|-1])
  }

  /* Returns a constant sequence of a given length. */
  opaque function Repeat<T>(v: T, length: nat): (xs: seq<T>)
    ensures |xs| == length
    ensures forall i: nat | i < |xs| :: xs[i] == v
  {
    if length == 0 then
      []
    else
      [v] + Repeat(v, length - 1)
  }

  /* Unzips a sequence that contains pairs into two separate sequences. */
  opaque function Unzip<A, B>(xs: seq<(A, B)>): (seq<A>, seq<B>)
    ensures |Unzip(xs).0| == |Unzip(xs).1| == |xs|
    ensures forall i {:trigger Unzip(xs).0[i]} {:trigger Unzip(xs).1[i]}
              :: 0 <= i < |xs| ==> (Unzip(xs).0[i], Unzip(xs).1[i]) == xs[i]
  {
    if |xs| == 0 then ([], [])
    else
      var (a, b):= Unzip(DropLast(xs));
      (a + [Last(xs).0], b + [Last(xs).1])
  }

  /* Zips two sequences of equal length into one sequence that consists of pairs. */
  opaque function Zip<A, B>(xs: seq<A>, ys: seq<B>): seq<(A, B)>
    requires |xs| == |ys|
    ensures |Zip(xs, ys)| == |xs|
    ensures forall i {:trigger Zip(xs, ys)[i]} :: 0 <= i < |Zip(xs, ys)| ==> Zip(xs, ys)[i] == (xs[i], ys[i])
    ensures Unzip(Zip(xs, ys)).0 == xs
    ensures Unzip(Zip(xs, ys)).1 == ys
  {
    if |xs| == 0 then []
    else Zip(DropLast(xs), DropLast(ys)) + [(Last(xs), Last(ys))]
  }


  function MaxBy<T>(s: seq<T>, lessThan: (T, T) -> bool): T
    requires |s| > 0
    decreases |s|
  {
    MaxByHelper(s, 1, s[0], lessThan)
  }

  function MaxByHelper<T>(s: seq<T>, idx: nat, current: T, lessThan: (T, T) -> bool): T
    requires idx <= |s|
    decreases |s| - idx
  {
    if idx == |s| then
      current
    else
      var next := if lessThan(current, s[idx]) then s[idx] else current;
      MaxByHelper(s, idx + 1, next, lessThan)
  }

  function MinBy<T>(s: seq<T>, lessThan: (T, T) -> bool): T
    requires |s| > 0
    decreases |s|
  {
    MinByHelper(s, 1, s[0], lessThan)
  }

  function MinByHelper<T>(s: seq<T>, idx: nat, current: T, lessThan: (T, T) -> bool): T
    requires idx <= |s|
    decreases |s| - idx
  {
    if idx == |s| then
      current
    else
      var next := if lessThan(s[idx], current) then s[idx] else current;
      MinByHelper(s, idx + 1, next, lessThan)
  }

  /* Unzipping and zipping a sequence results in the original sequence */
  lemma LemmaZipOfUnzip<A, B>(xs: seq<(A, B)>)
    ensures Zip(Unzip(xs).0, Unzip(xs).1) == xs
  {
  }

  /* If a predicate is true for every member of a sequence as a collection,
     it is true at every index of the sequence.
     Useful for converting quantifiers between the two forms
     to satisfy a precondition in the latter form. */
  lemma MembershipImpliesIndexing<T>(p: T -> bool, xs: seq<T>)
    requires forall t | t in xs :: p(t)
    ensures forall i | 0 <= i < |xs| :: p(xs[i])
  {
  }

  /**********************************************************
   *
   *  Extrema in Sequences
   *
   ***********************************************************/

  /* Returns the maximum integer value in a non-empty sequence of integers. */
  opaque function Max(xs: seq<int>): int
    requires 0 < |xs|
    ensures forall k :: k in xs ==> Max(xs) >= k
    ensures Max(xs) in xs
  {
    assert xs == [xs[0]] + xs[1..];
    if |xs| == 1 then xs[0] else Math.Max(xs[0], Max(xs[1..]))
  }

  /* The maximum of the concatenation of two non-empty sequences is greater than or
     equal to the maxima of its two non-empty subsequences. */
  lemma LemmaMaxOfConcat(xs: seq<int>, ys: seq<int>)
    requires 0 < |xs| && 0 < |ys|
    ensures Max(xs+ys) >= Max(xs)
    ensures Max(xs+ys) >= Max(ys)
    ensures forall i {:trigger i in [Max(xs + ys)]} :: i in xs + ys ==> Max(xs + ys) >= i
  {
    reveal Max;
    if |xs| == 1 {
    } else {
      assert xs[1..] + ys == (xs + ys)[1..];
      LemmaMaxOfConcat(xs[1..], ys);
    }
  }

  /* Returns the minimum integer value in a non-empty sequence of integers. */
  opaque function Min(xs: seq<int>): int
    requires 0 < |xs|
    ensures forall k :: k in xs ==> Min(xs) <= k
    ensures Min(xs) in xs
  {
    assert xs == [xs[0]] + xs[1..];
    if |xs| == 1 then xs[0] else Math.Min(xs[0], Min(xs[1..]))
  }

  /* The minimum of the concatenation of two non-empty sequences is
     less than or equal to the minima of its two non-empty subsequences. */
  lemma LemmaMinOfConcat(xs: seq<int>, ys: seq<int>)
    requires 0 < |xs| && 0 < |ys|
    ensures Min(xs+ys) <= Min(xs)
    ensures Min(xs+ys) <= Min(ys)
    ensures forall i :: i in xs + ys ==> Min(xs + ys) <= i
  {
    reveal Min;
    if |xs| == 1 {
    } else {
      assert xs[1..] + ys == (xs + ys)[1..];
      LemmaMinOfConcat(xs[1..], ys);
    }
  }

  /* The maximum element in a non-empty sequence is greater than or equal to
     the maxima of its non-empty subsequences. */
  lemma LemmaSubseqMax(xs: seq<int>, from: nat, to: nat)
    requires from < to <= |xs|
    ensures Max(xs[from..to]) <= Max(xs)
  {
    var subseq := xs[from..to];
    var subseqMax := Max(subseq);
    assert forall x | x in subseq :: x in xs[from..];
    assert subseqMax in subseq;
    assert subseqMax in xs;
  }

  /* The minimum element of a non-empty sequence is less than or equal
     to the minima of its non-empty subsequences. */
  lemma LemmaSubseqMin(xs: seq<int>, from: nat, to: nat)
    requires from < to <= |xs|
    ensures Min(xs[from..to]) >= Min(xs)
  {
    var subseq := xs[from..to];
    var subseqMin := Min(subseq);
    assert forall x | x in subseq :: x in xs[from..];
    assert subseqMin in subseq;
    assert subseqMin in xs;
  }

  /**********************************************************
   *
   *  Sequences of Sequences
   *
   ***********************************************************/

  /* Flattens a sequence of sequences into a single sequence by concatenating
     subsequences, starting from the first element. */
  function Flatten<T>(xs: seq<seq<T>>): seq<T>
    decreases |xs|
  {
    if |xs| == 0 then []
    else xs[0] + Flatten(xs[1..])
  }

  /* Flattening sequences of sequences is distributive over concatenation. That is, concatenating
     the flattening of two sequences of sequences is the same as flattening the
     concatenation of two sequences of sequences. */
  @IsolateAssertions
  lemma LemmaFlattenConcat<T>(xs: seq<seq<T>>, ys: seq<seq<T>>)
    ensures Flatten(xs + ys) == Flatten(xs) + Flatten(ys)
  {
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      calc == {
        Flatten(xs + ys);
        { assert (xs + ys)[0] == xs[0];  assert (xs + ys)[1..] == xs[1..] + ys; }
        xs[0] + Flatten(xs[1..] + ys);
        xs[0] + Flatten(xs[1..]) + Flatten(ys);
        Flatten(xs) + Flatten(ys);
      }
    }
  }

  /* Flattens a sequence of sequences into a single sequence by concatenating
     subsequences in reverse order, i.e. starting from the last element. */
  function FlattenReverse<T>(xs: seq<seq<T>>): seq<T>
    decreases |xs|
  {
    if |xs| == 0 then []
    else FlattenReverse(DropLast(xs)) + Last(xs)
  }

  /* Flattening sequences of sequences in reverse order is distributive over concatentation.
     That is, concatenating the flattening of two sequences of sequences in reverse
     order is the same as flattening the concatenation of two sequences of sequences
     in reverse order. */
  lemma LemmaFlattenReverseConcat<T>(xs: seq<seq<T>>, ys: seq<seq<T>>)
    ensures FlattenReverse(xs + ys) == FlattenReverse(xs) + FlattenReverse(ys)
  {
    if |ys| == 0 {
      assert FlattenReverse(ys) == [];
      assert xs + ys == xs;
    } else {
      calc == {
        FlattenReverse(xs + ys);
        { assert Last(xs + ys) == Last(ys);  assert DropLast(xs + ys) == xs + DropLast(ys); }
        FlattenReverse(xs + DropLast(ys)) + Last(ys);
        FlattenReverse(xs) + FlattenReverse(DropLast(ys)) + Last(ys);
        FlattenReverse(xs) + FlattenReverse(ys);
      }
    }
  }

  /* Flattening sequences of sequences in order (starting from the beginning)
     and in reverse order (starting from the end) results in the same sequence. */
  lemma LemmaFlattenAndFlattenReverseAreEquivalent<T>(xs: seq<seq<T>>)
    ensures Flatten(xs) == FlattenReverse(xs)
  {
    if |xs| == 0 {
    } else {
      calc == {
        FlattenReverse(xs);
        FlattenReverse(DropLast(xs)) + Last(xs);
        { LemmaFlattenAndFlattenReverseAreEquivalent(DropLast(xs)); }
        Flatten(DropLast(xs)) + Last(xs);
        Flatten(DropLast(xs)) + Flatten([Last(xs)]);
        { LemmaFlattenConcat(DropLast(xs), [Last(xs)]);
          assert xs == DropLast(xs) + [Last(xs)]; }
        Flatten(xs);
      }
    }
  }

  /* The length of a flattened sequence of sequences xs is greater than or
     equal to any of the lengths of the elements of xs.  */
  lemma LemmaFlattenLengthGeSingleElementLength<T>(xs: seq<seq<T>>, i: int)
    requires 0 <= i < |xs|
    ensures |FlattenReverse(xs)| >= |xs[i]|
  {
    if i < |xs| - 1 {
      LemmaFlattenLengthGeSingleElementLength(xs[..|xs|-1], i);
    }
  }

  /* The length of a flattened sequence of sequences xs is less than or equal
     to the length of xs multiplied by a number not smaller than the length of the
     longest sequence in xs. */
  lemma LemmaFlattenLengthLeMul<T>(xs: seq<seq<T>>, j: int)
    requires forall i | 0 <= i < |xs| :: |xs[i]| <= j
    ensures |FlattenReverse(xs)| <= |xs| * j
  {
    if |xs| == 0 {
    } else {
      LemmaFlattenLengthLeMul(xs[..|xs|-1], j);
      assert |FlattenReverse(xs[..|xs|-1])| <= (|xs|-1) * j;
    }
  }

  /* Join a sequence of sequences using a separator sequence.
     Particularly useful for strings (since string is just an alias for seq<char>) */
  function Join<T>(seqs: seq<seq<T>>, separator: seq<T>) : seq<T> {
    if |seqs| == 0 then []
    else if |seqs| == 1 then seqs[0]
    else seqs[0] + separator + Join(seqs[1..], separator)
  }

  lemma LemmaJoinWithEmptySeparator(seqs: seq<string>)
    ensures Flatten(seqs) == Join(seqs, [])
  {}

  @TailRecursion
  function Split<T(==)>(s: seq<T>, delim: T): (res: seq<seq<T>>)
    ensures delim !in s ==> res == [s]
    ensures s == [] ==> res == [[]]
    ensures 0 < |res|
    ensures forall i :: 0 <= i < |res| ==> delim !in res[i]
    ensures Join(res, [delim]) == s
    decreases |s|
  {
    var i := IndexOfOption(s, delim);
    if i.Some? then [s[..i.value]] + Split(s[(i.value + 1)..], delim) else [s]
  }

  /* Split on first occurrence of delim, which must exist */
  @TailRecursion
  function SplitOnce<T(==)>(s: seq<T>, delim: T): (res : (seq<T>,seq<T>))
    requires delim in s
    ensures res.0 + [delim] + res.1 == s
    ensures !(delim in res.0)
  {
    var i := IndexOfOption(s, delim);
    assert i.Some?;
    (s[..i.value], s[(i.value + 1)..])
  }

  // split on first occurrence of delim, return None if delim not present
  @TailRecursion
  function SplitOnceOption<T(==)>(s: seq<T>, delim: T): (res : Option<(seq<T>,seq<T>)>)
    ensures res.Some? ==> res.value.0 + [delim] + res.value.1 == s
    ensures res.None? ==> !(delim in s)
    ensures res.Some? ==> !(delim in res.value.0)
  {
    var i :- IndexOfOption(s, delim);
    Some((s[..i], s[(i + 1)..]))
  }

  @ResourceLimit("1e6")
  @IsolateAssertions
  lemma {:induction false} WillSplitOnDelim<T>(s: seq<T>, delim: T, prefix: seq<T>)
    requires |prefix| < |s|
    requires forall i :: 0 <= i < |prefix| ==> prefix[i] == s[i]
    requires delim !in prefix && s[|prefix|] == delim
    ensures Split(s, delim) == [prefix] + Split(s[|prefix| + 1..], delim)
  {
    hide *;
    calc {
      Split(s, delim);
    ==  { reveal Split(); }
      var i := IndexOfOption(s, delim);
      if i.Some? then [s[..i.value]] + Split(s[i.value + 1..], delim) else [s];
    ==  { IndexOfOptionLocatesElem(s, delim, |prefix|); assert IndexOfOption(s, delim).Some?; }
      [s[..|prefix|]] + Split(s[|prefix| + 1..], delim);
    ==  { assert s[..|prefix|] == prefix; }
      [prefix] + Split(s[|prefix| + 1..], delim);
    }
  }

  lemma WillNotSplitWithOutDelim<T>(s: seq<T>, delim: T)
    requires delim !in s
    ensures Split(s, delim) == [s]
  {
    calc {
      Split(s, delim);
    ==
      var i := IndexOfOption(s, delim);
      if i.Some? then [s[..i.value]] + Split(s[i.value+1..], delim) else [s];
    ==  { IndexOfOptionLocatesElem(s, delim, |s|); }
      [s];
    }
  }

  lemma IndexOfOptionLocatesElem<T>(s: seq<T>, c: T, elemIndex: nat)
    requires 0 <= elemIndex <= |s|
    requires forall i :: 0 <= i < elemIndex ==> s[i] != c
    requires elemIndex == |s| || s[elemIndex] == c
    ensures IndexOfOption(s, c) == if elemIndex == |s| then None else Some(elemIndex)
    decreases elemIndex
  {}

  /**********************************************************
   *
   *  Higher-Order Sequence Functions
   *
   ***********************************************************/

  /* Returns the sequence one obtains by applying a function to every element
     of a sequence. */
  opaque function Map<T, R>(f: T ~> R, xs: seq<T>): (result: seq<R>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    ensures |result| == |xs|
    ensures forall i {:trigger result[i]} :: 0 <= i < |xs| ==> result[i] == f(xs[i])
    reads set i, o | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
  {
    if |xs| == 0 then []
    else [f(xs[0])] + Map(f, xs[1..])
  }

  function MapPartialFunction<T, R>(f: T --> R, xs: seq<T>): (result: seq<R>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
  {
    Map(f, xs)
  }

  /* Applies a function to every element of a sequence, returning a Result value (which is a
     failure-compatible type). Returns either a failure, or, if successful at every element,
     the transformed sequence.  */
  opaque function MapWithResult<T, R, E>(f: (T ~> Result<R, E>), xs: seq<T>): (result: Result<seq<R>, E>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    ensures result.Success? ==>
              && |result.value| == |xs|
              && (forall i :: 0 <= i < |xs| ==>
                                && f(xs[i]).Success?
                                && result.value[i] == f(xs[i]).value)
    reads set i, o | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
  {
    if |xs| == 0 then Success([])
    else
      var head :- f(xs[0]);
      var tail :- MapWithResult(f, xs[1..]);
      Success([head] + tail)
  }

  /* Applying a function to a sequence  is distributive over concatenation. That is, concatenating
     two sequences and then applying Map is the same as applying Map to each sequence separately,
     and then concatenating the two resulting sequences. */
  lemma {:induction false} LemmaMapDistributesOverConcat<T,R>(f: (T ~> R), xs: seq<T>, ys: seq<T>)
    requires X: forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    requires Y: forall j :: 0 <= j < |ys| ==> f.requires(ys[j])
    ensures Map(f, xs + ys) == Map(f, xs) + Map(f, ys)
  {
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      calc {
        Map(f, reveal X, Y; xs + ys);
        { assert (xs + ys)[0] == xs[0]; assert (xs + ys)[1..] == xs[1..] + ys; }
        Map(f, [xs[0]]) + Map(f, xs[1..] + ys);
        Map(f, [xs[0]]) + Map(f, reveal X; xs[1..]) + Map(f, reveal Y; ys);
        {assert [(xs + ys)[0]] + xs[1..] + ys == xs + ys;}
        Map(f, xs) + Map(f, ys);
      }
    }
  }

  lemma {:induction false} LemmaMapPartialFunctionDistributesOverConcat<T, R>(f: T --> R, xs: seq<T>, ys: seq<T>)
    requires X: forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    requires Y: forall j :: 0 <= j < |ys| ==> f.requires(ys[j])
    ensures MapPartialFunction(f, xs + ys) == MapPartialFunction(f, xs) + MapPartialFunction(f, ys)
  {
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      calc {
        MapPartialFunction(f, reveal X, Y; xs + ys);
        { assert (xs + ys)[0] == xs[0]; assert (xs + ys)[1..] == xs[1..] + ys; }
        MapPartialFunction(f, [xs[0]]) + MapPartialFunction(f, xs[1..] + ys);
        MapPartialFunction(f, [xs[0]]) + MapPartialFunction(f, reveal X; xs[1..]) + MapPartialFunction(f, reveal Y; ys);
        { assert [(xs + ys)[0]] + xs[1..] + ys == xs + ys; }
        MapPartialFunction(f, xs) + MapPartialFunction(f, ys);
      }
    }
  }

  /* Returns the subsequence consisting of those elements of a sequence that satisfy a given
     predicate. */
  opaque function Filter<T>(f: (T ~> bool), xs: seq<T>): (result: seq<T>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    ensures |result| <= |xs|
    ensures forall i: nat | i < |result| :: f.requires(result[i]) && f(result[i])
    reads set i, o | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
  {
    if |xs| == 0 then []
    else (if f(xs[0]) then [xs[0]] else []) + Filter(f, xs[1..])
  }

  /* Filtering a sequence is distributive over concatenation. That is, concatenating two sequences
     and then using "Filter" is the same as using "Filter" on each sequence separately, and then
     concatenating the two resulting sequences. */
  @IsolateAssertions
  lemma {:induction false}
    LemmaFilterDistributesOverConcat<T>(f: T ~> bool, xs: seq<T>, ys: seq<T>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    requires forall j :: 0 <= j < |ys| ==> f.requires(ys[j])
    ensures Filter(f, xs + ys) == Filter(f, xs) + Filter(f, ys)
  {
    hide *;
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      calc {
        Filter(f, xs + ys);
        {
          reveal Filter;
          assert (xs + ys)[0] == xs[0]; assert (xs + ys)[1..] == xs[1..] + ys;
        }
        Filter(f, [xs[0]]) + Filter(f, xs[1..] + ys);
        { LemmaFilterDistributesOverConcat(f, xs[1..], ys); }
        Filter(f, [xs[0]]) + (Filter(f, xs[1..]) + Filter(f, ys));
        {
          reveal Filter;
          assert [(xs + ys)[0]] + (xs[1..] + ys) == xs + ys; }
        Filter(f, xs) + Filter(f, ys);
      }
    }
  }

  /* Folds a sequence xs from the left (the beginning), by repeatedly acting on the accumulator
     init via the function f. */
  function FoldLeft<A, T>(f: (A, T) -> A, init: A, xs: seq<T>): A
  {
    if |xs| == 0 then init
    else FoldLeft(f, f(init, xs[0]), xs[1..])
  }

  /* Folding to the left is distributive over concatenation. That is, concatenating two
     sequences and then folding them to the left, is the same as folding to the left the
     first sequence and using the result to fold to the left the second sequence. */
  lemma LemmaFoldLeftDistributesOverConcat<A, T>(f: (A, T) -> A, init: A, xs: seq<T>, ys: seq<T>)
    ensures FoldLeft(f, init, xs + ys) == FoldLeft(f, FoldLeft(f, init, xs), ys)
  {
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      assert |xs| >= 1;
      assert ([xs[0]] + xs[1..] + ys)[0] == xs[0];
      calc {
        FoldLeft(f, FoldLeft(f, init, xs), ys);
        FoldLeft(f, FoldLeft(f, f(init, xs[0]), xs[1..]), ys);
        { LemmaFoldLeftDistributesOverConcat(f, f(init, xs[0]), xs[1..], ys); }
        FoldLeft(f, f(init, xs[0]), xs[1..] + ys);
        { assert (xs + ys)[0] == xs[0];
          assert (xs + ys)[1..] == xs[1..] + ys; }
        FoldLeft(f, init, xs + ys);
      }
    }
  }

  /* Is true, if inv is an invariant under stp, which is a relational
     version of the function f passed to fold. */
  ghost predicate InvFoldLeft<A(!new), B(!new)>(inv: (B, seq<A>) -> bool,
                                                stp: (B, A, B) -> bool)
  {
    forall x: A, xs: seq<A>, b: B, b': B ::
      inv(b, [x] + xs) && stp(b, x, b') ==> inv(b', xs)
  }

  /* inv(b, xs) ==> inv(FoldLeft(f, b, xs), []). */
  lemma LemmaInvFoldLeft<A(!new), B(!new)>(inv: (B, seq<A>) -> bool,
                                           stp: (B, A, B) -> bool,
                                           f: (B, A) -> B,
                                           b: B,
                                           xs: seq<A>)
    requires InvFoldLeft(inv, stp)
    requires forall b, a :: stp(b, a, f(b, a))
    requires inv(b, xs)
    ensures inv(FoldLeft(f, b, xs), [])
  {
    if xs == [] {
    } else {
      assert [xs[0]] + xs[1..] == xs;
      LemmaInvFoldLeft(inv, stp, f, f(b, xs[0]), xs[1..]);
    }
  }

  /* Folds a sequence xs from the right (the end), by acting on the accumulator init via the
     function f. */
  function FoldRight<A, T>(f: (T, A) -> A, xs: seq<T>, init: A): A
  {
    if |xs| == 0 then init
    else f(xs[0], FoldRight(f, xs[1..], init))
  }

  /* Folding to the right is (contravariantly) distributive over concatenation. That is, concatenating
     two sequences and then folding them to the right, is the same as folding to the right
     the second sequence and using the result to fold to the right the first sequence. */
  lemma LemmaFoldRightDistributesOverConcat<A, T>(f: (T, A) -> A, init: A, xs: seq<T>, ys: seq<T>)
    ensures FoldRight(f, xs + ys, init) == FoldRight(f, xs, FoldRight(f, ys, init))
  {
    if |xs| == 0 {
      assert xs + ys == ys;
    } else {
      calc {
        FoldRight(f, xs, FoldRight(f, ys, init));
        f(xs[0], FoldRight(f, xs[1..], FoldRight(f, ys, init)));
        f(xs[0], FoldRight(f, xs[1..] + ys, init));
        { assert (xs + ys)[0] == xs[0];
          assert (xs +ys)[1..] == xs[1..] + ys; }
        FoldRight(f, xs + ys, init);
      }
    }
  }

  /* Is true, if inv is an invariant under stp, which is a relational version
     of the function f passed to fold. */
  ghost predicate InvFoldRight<A(!new), B(!new)>(inv: (seq<A>, B) -> bool,
                                                 stp: (A, B, B) -> bool)
  {
    forall x: A, xs: seq<A>, b: B, b': B ::
      inv(xs, b) && stp(x, b, b') ==> inv(([x] + xs), b')
  }

  /* inv([], b) ==> inv(xs, FoldRight(f, xs, b)) */
  lemma LemmaInvFoldRight<A(!new), B(!new)>(inv: (seq<A>, B) -> bool,
                                            stp: (A, B, B) -> bool,
                                            f: (A, B) -> B,
                                            b: B,
                                            xs: seq<A>)
    requires InvFoldRight(inv, stp)
    requires forall a, b :: stp(a, b, f(a, b))
    requires inv([], b)
    ensures inv(xs, FoldRight(f, xs, b))
  {
    if xs == [] {
    } else {
      assert [xs[0]] + xs[1..] == xs;
    }
  }

  /****************************
   **  Sorting sequences
   ***************************** */

  //Splits a sequence in two, sorts the two subsequences (recursively), and merges the two sorted sequences using `MergeSortedWith`
  function MergeSortBy<T(!new)>(lessThanOrEq: (T, T) -> bool, a: seq<T>): (result :seq<T>)
    requires TotalOrdering(lessThanOrEq)
    ensures multiset(a) == multiset(result)
    ensures SortedBy(lessThanOrEq, result)
  {
    if |a| <= 1 then
      a
    else
      var splitIndex := |a| / 2;
      var left, right := a[..splitIndex], a[splitIndex..];

      assert a == left + right;

      var leftSorted := MergeSortBy(lessThanOrEq, left);
      var rightSorted := MergeSortBy(lessThanOrEq, right);

      MergeSortedWith(leftSorted, rightSorted, lessThanOrEq)
  }

  // Helper function for MergeSortBy
  @TailRecursion
  function MergeSortedWith<T(!new)>(left: seq<T>, right: seq<T>, lessThanOrEq: (T, T) -> bool) : (result :seq<T>)
    requires SortedBy(lessThanOrEq, left)
    requires SortedBy(lessThanOrEq, right)
    requires TotalOrdering(lessThanOrEq)
    ensures multiset(left + right) == multiset(result)
    ensures SortedBy(lessThanOrEq, result)
  {
    if |left| == 0 then
      right
    else if |right| == 0 then
      left
    else if lessThanOrEq(left[0], right[0]) then
      LemmaNewFirstElementStillSortedBy(left[0], MergeSortedWith(left[1..], right, lessThanOrEq), lessThanOrEq);
      assert left == [left[0]] + left[1..];

      [left[0]] + MergeSortedWith(left[1..], right, lessThanOrEq)

    else
      LemmaNewFirstElementStillSortedBy(right[0], MergeSortedWith(left, right[1..], lessThanOrEq), lessThanOrEq);
      assert right == [right[0]] + right[1..];

      [right[0]] + MergeSortedWith(left, right[1..], lessThanOrEq)
  }

  lemma LemmaNewFirstElementStillSortedBy<T(!new)>(newFirst: T, s: seq<T>, lessOrEqual: (T, T) -> bool)
    requires SortedBy(lessOrEqual, s)
    requires |s| == 0 || lessOrEqual(newFirst, s[0])
    requires TotalOrdering(lessOrEqual)
    ensures SortedBy(lessOrEqual, [newFirst] + s)
  {}

  /* Proves that any two sequences that are sorted by a total order and that have the same elements are equal. */
  lemma SortedUnique<T(!new)>(xs: seq<T>, ys: seq<T>, R: (T, T) -> bool)
    requires SortedBy(R, xs)
    requires SortedBy(R, ys)
    requires TotalOrdering(R)
    requires multiset(xs) == multiset(ys)
    ensures xs == ys
  {
    if xs == [] {
      assert multiset(xs) == multiset{};
      assert multiset(ys) == multiset{};
      assert ys == [];
    } else {
      assert xs == [xs[0]] + xs[1..];
      assert ys == [ys[0]] + ys[1..];
      assert multiset(xs[1..]) == multiset(xs) - multiset{xs[0]};
      assert multiset(ys[1..]) == multiset(ys) - multiset{ys[0]};
      assert multiset(xs[1..]) == multiset(ys[1..]);
      SortedUnique(xs[1..], ys[1..], R);
    }
  }

  /**********************************************************
   *
   *  Partitions
   *
   ***********************************************************/

  predicate All<T>(s: seq<T>, p: T -> bool) {
    forall i {:trigger s[i]} | 0 <= i < |s| :: p(s[i])
  }

  predicate AllNot<T>(s: seq<T>, p: T -> bool) {
    forall i {:trigger s[i]} | 0 <= i < |s| :: !p(s[i])
  }

  lemma AllDecomposition<T>(left: seq<T>, right: seq<T>, p: T -> bool)
    requires All(left + right, p)
    ensures All(left, p)
    ensures All(right, p)
  {
    forall i: nat | i < |left| ensures p(left[i]) {
      assert (left + right)[i] == left[i];
    }
    forall i: nat | i < |right| ensures p(right[i]) {
      assert (left + right)[|left| + i] == right[i];
    }
  }

  lemma AllNotDecomposition<T>(left: seq<T>, right: seq<T>, p: T -> bool)
    requires AllNot(left + right, p)
    ensures AllNot(left, p)
    ensures AllNot(right, p)
  {
    forall i: nat | i < |left| ensures !p(left[i]) {
      assert (left + right)[i] == left[i];
    }
    forall i: nat | i < |right| ensures !p(right[i]) {
      assert (left + right)[|left| + i] == right[i];
    }
  }

  predicate Partitioned<T>(s: seq<T>, p: T -> bool) {
    if s == [] then
      true
    else if p(s[0]) then
      Partitioned(s[1..], p)
    else
      AllNot(s[1..], p)
  }

  lemma AllImpliesPartitioned<T>(s: seq<T>, p: T -> bool)
    requires All(s, p)
    ensures Partitioned(s, p)
  {}

  lemma AllNotImpliesPartitioned<T>(s: seq<T>, p: T -> bool)
    requires AllNot(s, p)
    ensures Partitioned(s, p)
  {}

  lemma PartitionedFirstFalseImpliesAllNot<T>(s: seq<T>, p: T -> bool)
    requires Partitioned(s, p)
    requires 0 < |s|
    requires !p(First(s))
    ensures AllNot(s, p)
  {}

  lemma PartitionedLastTrueImpliesAll<T>(s: seq<T>, p: T -> bool)
    requires Partitioned(s, p)
    requires 0 < |s|
    requires p(Last(s))
    ensures All(s, p)
  {}

  lemma PartitionedCompositionRight<T>(left: seq<T>, right: seq<T>, p: T -> bool)
    requires Partitioned(left, p)
    requires AllNot(right, p)
    ensures Partitioned(left + right, p)
  {
    if left == [] {
    } else {
      if p(left[0]) {
        PartitionedCompositionRight(left[1..], right, p);
        assert left == [left[0]] + left[1..];
        PartitionedCompositionLeft([left[0]], left[1..] + right, p);
        assert Partitioned([left[0]] + (left[1..] + right), p);
        assert left + right == [left[0]] + (left[1..] + right);
      } else {
      }
    }
  }

  lemma PartitionedCompositionLeft<T>(left: seq<T>, right: seq<T>, p: T -> bool)
    requires All(left, p)
    requires Partitioned(right, p)
    ensures Partitioned(left + right, p)
  {
    if left == [] {
      assert left + right == right;
    } else {
      PartitionedCompositionLeft(left[1..], right, p);
      assert left + right == [left[0]] + (left[1..] + right);
    }
  }

  lemma PartitionedDecomposition<T>(left: seq<T>, right: seq<T>, p: T -> bool)
    requires Partitioned(left + right, p)
    ensures Partitioned(left, p)
    ensures Partitioned(right, p)
  {
    if left == [] {
      assert right == left + right;
    } else {
      if !p(left[0]) {
        PartitionedFirstFalseImpliesAllNot(left + right, p);
        AllNotDecomposition(left, right, p);
        assert AllNot(left, p);
        PartitionedDecomposition(left[1..], right, p);
      } else {
        var combined := left + right;
        assert p(combined[0]);
        assert Partitioned(combined[1..], p);
        assert combined[1..] == left[1..] + right;
        PartitionedDecomposition(left[1..], right, p);
      }
    }
  }

  /**********************************************************
   *
   *  Slices
   *  Optimization on sequences when there is a lot of slicing
   *
   ***********************************************************/

  datatype Slice<T> = Slice(data: seq<T>, start: int, end: int) {
    /* Checks if the slice indices are valid for the underlying data sequence. */
    ghost predicate Valid() {
      0 <= start <= end <= |data|
    }

    /* Returns the slice as a sequence. */
    function View(): seq<T>
      requires Valid()
    {
      data[start..end]
    }

    /* Returns the length of the slice. */
    function Length(): nat
      requires Valid()
    {
      end - start
    }

    /* Returns the element at the specified index within the slice. */
    function At(i: int): (result: T)
      requires Valid()
      requires 0 <= i < Length()
      ensures result == View()[i]
    {
      data[start + i]
    }

    /* Returns a new slice that drops elements from the beginning of this slice. */
    function Drop(firstIncludedIndex: int): (result: Slice<T>)
      requires Valid()
      requires 0 <= firstIncludedIndex <= Length()
      ensures result.Valid()
      ensures result.View() == View()[firstIncludedIndex..]
    {
      Slice(data, start + firstIncludedIndex, end)
    }

    /* Returns a sub-slice from this slice using the specified range. */
    function Sub(firstIncludedIndex: int, lastExcludedIndex: int): (result: Slice<T>)
      requires Valid()
      requires 0 <= firstIncludedIndex <= lastExcludedIndex <= Length()
      ensures result.Valid()
      ensures result.View() == View()[firstIncludedIndex..lastExcludedIndex]
    {
      PrefixRestrict(firstIncludedIndex, lastExcludedIndex);
      Slice(data, start + firstIncludedIndex, start + lastExcludedIndex)
    }

    /* Proves that slicing a prefix of data is equivalent to slicing the full data within the same range. */
    lemma PrefixRestrict(firstIncludedIndex: int, lastExcludedIndex: int)
      requires Valid()
      requires 0 <= firstIncludedIndex <= lastExcludedIndex <= Length()
      decreases |data| - end
      ensures data[start..][firstIncludedIndex..lastExcludedIndex] == data[start..end][firstIncludedIndex..lastExcludedIndex]
    {
      if end == |data| {
        assert data[start..end] == data[start..];
      } else {
        var before := data[start .. end][firstIncludedIndex .. lastExcludedIndex];
        var after := data[start .. end + 1][firstIncludedIndex .. lastExcludedIndex];
        calc {
          data[start .. end][firstIncludedIndex .. lastExcludedIndex];
          {
            assert |before| == |after|;
            assert forall i | 0 <= i < |before| :: before[i] == after[i];
          }
          data[start .. end + 1][firstIncludedIndex .. lastExcludedIndex];
        }
        Slice(data, start, end+1).PrefixRestrict(firstIncludedIndex, lastExcludedIndex);
      }
    }
  }

}
