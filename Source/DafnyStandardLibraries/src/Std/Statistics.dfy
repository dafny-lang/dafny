module ExternalMath {
  function {:extern} Sqrt(x: real): real
    requires x >= 0.0
    ensures Sqrt(x) >= 0.0
    ensures var result := Sqrt(x); result * result <= x + 0.0000001
    ensures var result := Sqrt(x); result * result >= x - 0.0000001
}

module Std.Statistics {
  import opened ExternalMath
  import opened Std.Collections.Seq

  // A function to sum the elements of a sequence
  function Sum(s: seq<real>): real
  {
    if |s| == 0 then
      0.0
    else
      s[0] + Sum(s[1..])
  }

  // A function to compute the mean (average) as a real number
  function Mean(s: seq<real>): real
    requires |s| > 0
    ensures Mean(s) == Sum(s) / (|s| as real)
  {
    Sum(s) / (|s| as real)
  }

  // A helper function to calculate the sum of squared differences from a given mean
  function SumSquaredDifferences(s: seq<real>, avg: real): real
    ensures SumSquaredDifferences(s, avg) >= 0.0
  {
    if |s| == 0 then
      0.0
    else
      var diff := s[0] - avg;
      diff * diff + SumSquaredDifferences(s[1..], avg)
  }
  // Function to calculate the absolute value of a real number
  function RealAbs(x: real): real
    ensures RealAbs(x) >= 0.0
    ensures RealAbs(x) == x || RealAbs(x) == -x
  {
    if x >= 0.0 then x else -x
  }
  // Function to check if two real numbers are close within a given tolerance.
  function AreNear(a: real, b: real, epsilon: real): bool
    requires epsilon >= 0.0
    ensures AreNear(a, b, epsilon) == (RealAbs(a - b) <= epsilon)
  {
    RealAbs(a - b) <= epsilon
  }

  // A function to calculate Population Variance
  function VariancePopulation(s: seq<real>): real
    requires |s| > 0
    ensures VariancePopulation(s) >= 0.0
    ensures VariancePopulation(s) == SumSquaredDifferences(s, Mean(s)) / (|s| as real)
  {
    var avg := Mean(s);
    SumSquaredDifferences(s, avg) / (|s| as real)
  }

  // A function to calculate Sample Variance
  function VarianceSample(s: seq<real>): real
    requires |s| > 1
    ensures VarianceSample(s) >= 0.0
  {
    var avg := Mean(s);
    (SumSquaredDifferences(s, avg)) / ((|s| - 1) as real)
  }

  // A function to calculate Population Standard Deviation
  function StdDevPopulation(s: seq<real>): real
    requires |s| > 0
    ensures StdDevPopulation(s) >= 0.0
  {
    ExternalMath.Sqrt(VariancePopulation(s))
  }

  // A function to calculate Sample Standard Deviation
  function StdDevSample(s: seq<real>): real
    requires |s| > 1
    ensures StdDevSample(s) >= 0.0
  {
    ExternalMath.Sqrt(VarianceSample(s))
  }

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
