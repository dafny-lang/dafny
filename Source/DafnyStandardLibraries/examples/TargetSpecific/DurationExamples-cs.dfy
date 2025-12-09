/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
Includes comprehensive test methods for validating the functionality of each
operation using Dafny's {:test} annotation.

These tests serve as verification examples that work with Dafny's formal proofs.
*/


module TestDuration {
  import Std.Duration
  import opened Std.BoundedInts
  import opened Helpers
  import opened Std.Collections.Seq

  method {:test} TestOfParseString() {
    var parsedResult := Duration.ParseString("PT9650H30M45.123S");
    expect parsedResult.Success?;
    expect Duration.GetMilliseconds(parsedResult.value) == 123;
  }

  method {:test} TestArithmetic() {
    var d1 := Duration.Duration(1, 2);
    var d2 := Duration.Duration(1, 3);
    // Compute total ms
    var total1 := Duration.ToTotalMilliseconds(d1);
    AssertAndExpect(total1 == 1002);

    // Addition
    var d3 := Duration.Plus(d1, d2);
    AssertAndExpect(d3 == Duration.Duration(2, 5));

    //Minus
    var d4 := Duration.Minus(d2, d1);
    AssertAndExpect(d4 == Duration.Duration(0, 1));
  }

  method {:test} TestComparison() {
    var d1 := Duration.Duration(1, 2);
    var d2 := Duration.Duration(1, 3);

    // Comparison
    var cmp := Duration.Compare(d1, d2);
    AssertAndExpect(cmp == -1);

    // Equality
    AssertAndExpect(d1 == d1);
    AssertAndExpect(!(d1 == d2));
  }

  method {:test} TestScalingAndDivision() {
    var d := Duration.Duration(2, 500); // 2.5 seconds = 2500 ms
    var scaled := Duration.Scale(d, 2); // 5000 ms
    AssertAndExpect(Duration.ToTotalMilliseconds(scaled) == 5000);

    var divided := Duration.Divide(scaled, 2);
    AssertAndExpect(divided == d);

    var mod := Duration.Mod(scaled, d);
    AssertAndExpect(mod == Duration.FromMilliseconds(0));
  }

  method {:test} TestMinMax() {
    var d := Duration.Duration(2, 500);
    var scaled := Duration.Scale(d, 2);

    var dmin := Duration.Min(d, scaled);
    var dmax := Duration.Max(d, scaled);
    AssertAndExpect(dmin == d);
    AssertAndExpect(dmax == scaled);
  }

  method {:test} TestUnitConversions() {
    var oneSec := Duration.FromSeconds(1);
    AssertAndExpect(Duration.ToTotalMilliseconds(oneSec) == 1000);

    var oneMin := Duration.FromMinutes(1);
    AssertAndExpect(Duration.ToTotalMilliseconds(oneMin) == (60000 as int));

    var oneHour :=  Duration.Duration(3600, 0);
    AssertAndExpect(Duration.ToTotalMilliseconds(oneHour) == 3600000);
  }

  method {:test} TestEdgeCases() {
    var d5 := Duration.FromMilliseconds(1000);
    var d6 := Duration.FromMilliseconds(999);
    AssertAndExpect(Duration.Less(d6, d5));
    AssertAndExpect(!Duration.Less(d5, d6));
    AssertAndExpect(Duration.Compare(d5, d5) == 0);
    AssertAndExpect(Duration.Compare(d5, d6) == 1);
    AssertAndExpect(Duration.Compare(d6, d5) == -1);
  }

  method {:test} TestEpochDifference() {
    var e1: int := 5000;
    var e2: int := 8000;
    var dd := Duration.EpochDifference(e1, e2);
    AssertAndExpect(Duration.ToTotalMilliseconds(dd) == 3000);
  }

  method {:test} TestNormalization() {
    var d8 := Duration.FromMilliseconds(2500);
    AssertAndExpect(Duration.GetSeconds(d8) == 2);
    AssertAndExpect(Duration.GetMilliseconds(d8) == 500);
  }

  method {:test} TestLessOrEqual() {
    var d1 := Duration.FromSeconds(5);
    var d2 := Duration.FromSeconds(10);

    AssertAndExpect(Duration.LessOrEqual(d1, d2));
    AssertAndExpect(Duration.LessOrEqual(d1, d1));
    AssertAndExpect(!Duration.LessOrEqual(d2, d1));
  }

  method {:test} TestStringConversion() {
    var d := Duration.Duration(3665, 500);  // 1H1M5.500S
    var str := Duration.ToString(d);
    AssertAndExpect(str[0] == 'P');
    AssertAndExpect(str[1] == 'T');
  }

  method {:test} TestMaxByWithCompareHelper() {
    var d1 := Duration.Duration(1, 100);
    var d2 := Duration.Duration(2, 50);
    var d3 := Duration.Duration(0, 999);
    var durations := [d1, d2, d3];

    var maxD := MaxBy(durations, Duration.Less);
    var minD := MinBy(durations, Duration.Less);

    expect maxD == d2;
    expect minD == d3;
  }
}
