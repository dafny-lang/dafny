/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/
/**
XX
*/
module {:options "-functionSyntax:4"} DafnyStdLibs.Sequences.MergeSort {
  import opened Relations

  //Splits a sequence in two, sorts the two subsequences using itself, and merge the two sorted sequences using `MergeSortedWith`
  function MergeSortBy<T>(a: seq<T>, lessThanOrEq: (T, T) -> bool): (result :seq<T>)
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

      var leftSorted := MergeSortBy(left, lessThanOrEq);
      var rightSorted := MergeSortBy(right, lessThanOrEq);

      MergeSortedWith(leftSorted, rightSorted, lessThanOrEq)
  }

  function {:tailrecursion} MergeSortedWith<T>(left: seq<T>, right: seq<T>, lessThanOrEq: (T, T) -> bool) : (result :seq<T>)
    requires SortedBy(lessThanOrEq, left)
    requires SortedBy( lessThanOrEq, right)
    requires TotalOrdering(lessThanOrEq)
    ensures multiset(left + right) == multiset(result)
    ensures SortedBy(lessThanOrEq, result)
  {
    assume {:axiom} false;
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
}