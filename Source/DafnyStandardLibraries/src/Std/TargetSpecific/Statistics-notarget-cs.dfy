module ExternalMath {
  function {:extern}{:axiom} Sqrt(x: real): real
    requires x >= 0.0
    ensures Sqrt(x) >= 0.0
}

module Std.Statistics {
  import opened ExternalMath
  import opened Collections.Seq

  // A function to sum the elements of a sequence
  function Sum(s: seq<real>): real
  {
    SumHelper(s, 0.0)
  }

  // Helper function for Sum with the required attribute
  function {:tailrecursion} SumHelper(s: seq<real>, acc: real): real
    decreases s
  {
    if |s| == 0 then acc
    else SumHelper(s[1..], acc + s[0])
  }

  // A function to compute the mean (average) as a real number
  function Mean(s: seq<real>): real
    requires |s| > 0
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
  {
    if x >= 0.0 then x else -x
  }
  // Function to check if two real numbers are close within a given tolerance.
  function AreNear(a: real, b: real, epsilon: real): bool
    requires epsilon >= 0.0
  {
    RealAbs(a - b) <= epsilon
  }

  // A function to calculate Population Variance
  function VariancePopulation(s: seq<real>): real
    requires |s| > 0
    ensures VariancePopulation(s) >= 0.0
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
    var nMinus1 := ((|s| - 1) as real);
    assert nMinus1 > 0 as real;
    (SumSquaredDifferences(s, avg)) / nMinus1
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
  {
    // Existing merge sort utilized
    var sorted := MergeSortBy((x: real, y: real) => x <= y, a);
    if |a| % 2 == 1 then
      sorted[|a|/2]
    else
      (sorted[|a|/2 - 1] + sorted[|a|/2]) / 2.0
  }

  // The function to get a map to store the occurences of elements
  function {:tailrecursion} FrequencyTable(s: seq<real>, m: map<real, int> := map[]): map<real, int>
    ensures m.Keys <= FrequencyTable(s, m).Keys
    ensures forall x :: x in s ==> x in FrequencyTable(s, m)
  {
    if s == [] then
      m
    else
      var key := s[0];
      var newM :=
        if key in m then
          m[key := m[key] + 1]
        else
          m[key := 1];
      FrequencyTable(s[1..], newM)
  }

  // Final mode function that calls the frequencytable and modehelper
  function Mode(s: seq<real>): real
    requires |s| > 0
  {
    var freq := FrequencyTable(s);
    var keys := s;
    var best := s[0];
    var i := 0;


    var result :=
      if |keys| == 1 then best
      else
        ModeHelper(freq, keys, best, 0);

    result
  }

  // Helper function to calculate mode
  function {:tailrecursion} ModeHelper(freq: map<real,int>, keys: seq<real>, best: real, i: nat): real
    requires forall x :: x in keys ==> x in freq
    requires best in keys
    decreases |keys| - i

  {
    if i >= |keys| then best
    else
      var next := keys[i];
      var newBest :=
        if freq[next] > freq[best] then next else best;
      ModeHelper(freq, keys, newBest, i + 1)
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
