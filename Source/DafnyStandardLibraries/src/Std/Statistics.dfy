

module Std.Statistics {
  
  import opened Std.Collections.Seq

  // Median of a non-empty sequence of real numbers
  function Median(a: seq<real>): real
    requires |a| > 0
    ensures var sorted := MergeSortBy((x: real, y: real) => x <= y, a);
            if |a| % 2 == 1 then
              Median(a) == sorted[|a|/2]
            else
              Median(a) == (sorted[|a|/2 - 1] + sorted[|a|/2]) / 2.0
  {
    // Existing merge sort utilized
    var sorted := MergeSortBy((x: real, y: real) => x <= y, a);
    if |a| % 2 == 1 then
      sorted[|a|/2]
    else
      (sorted[|a|/2 - 1] + sorted[|a|/2]) / 2.0
  }

  //The function for keeping a Count of the elements. This will be recursively called
  function Count(s: seq<real>, v: real): nat
    decreases s
  {
    if |s| == 0 then 0
    else if s[0] == v then 1 + Count(s[1..], v)
    else Count(s[1..], v)
  }

  // The function for calcluating mode
  function Mode(s: seq<real>): real
    requires |s| > 0
    ensures Mode(s) in s
    ensures (forall x :: x in s ==> Count(s, x) <= Count(s, Mode(s)))
  {
    if |s| == 1 then s[0]
    else if Count(s, s[0]) >= Count(s[1..], Mode(s[1..])) then s[0]
    else Mode(s[1..])
  }

  // The function for calcluating range for a sequence which is the max element - min element
  function Range(s: seq<real>): real
    requires |s| > 0
    ensures Range(s) >= 0.0
  {
    var sorted := MergeSortBy((x: real, y: real) => x <= y, s);
    sorted[|s| - 1] - sorted[0]
  }


}
