// Test file for Optimized Duration Module
// This test is compatible with the optimized Duration_Optimized.dfy

include "../../src/Std/DateTime/Duration.dfy"

module TestDuration {
  import Std.Duration
  import opened Std.BoundedInts

  method TestOfParseString() {
    var parsedResult := Duration.ParseString("PT9650H30M45.123S");
    expect Duration.GetMilliseconds(parsedResult) == 123;
  }

  method TestBasicCreation() {
    var d1 := Duration.Duration(1, 2);
    assert d1.Valid();
    var d2 := Duration.Duration(1, 3);
    assert d2.Valid();
  }

  method TestArithmetic() {
    var d1 := Duration.Duration(1, 2);
    var d2 := Duration.Duration(1, 3);
    
    // Compute total ms
    var total1 := Duration.ToTotalMilliseconds(d1);
    assert total1 == 1002;
    
    // Addition
    var d3 := Duration.Plus(d1, d2);
    assert d3.Valid();
    
    // Subtraction (safe - d2 > d1, returns 0)
    var d4 := Duration.Minus(d1, d2);
    assert d4 == Duration.Duration(0, 0);
  }

  method TestComparison() {
    var d1 := Duration.Duration(1, 2);
    var d2 := Duration.Duration(1, 3);
    
    // Comparison
    var cmp := Duration.Compare(d1, d2);
    assert cmp == -1;
    
    // Equality
    assert d1 == d1;
    assert !(d1 == d2);
  
  }

  method TestScalingAndDivision() {
    var d := Duration.Duration(2, 500); // 2.5 seconds = 2500 ms
    var scaled := Duration.Scale(d, 2); // 5000 ms
    assert Duration.ToTotalMilliseconds(scaled) == 5000;
    assert scaled.Valid();
    
    var divided := Duration.Divide(scaled, 2);
    assert divided == d;
    
    var mod := Duration.Mod(scaled, d);
    assert mod == Duration.FromMilliseconds(0);

  }

  method TestMinMax() {
    var d := Duration.Duration(2, 500);
    var scaled := Duration.Scale(d, 2);
    
    var dmin := Duration.Min(d, scaled);
    var dmax := Duration.Max(d, scaled);
    assert dmin == d;
    assert dmax == scaled;
    
  }

  method TestUnitConversions() {
    var oneSec := Duration.FromSeconds(1);
    assert Duration.ToTotalMilliseconds(oneSec) == 1000;
    
    var oneMin := Duration.FromMinutes(1);
    assert Duration.ToTotalMilliseconds(oneMin) == 60000;
    
    var oneHour := Duration.FromHours(1);
    assert Duration.ToTotalMilliseconds(oneHour) == 3600000;
    
    var oneDay := Duration.FromDays(1);
    assert Duration.ToTotalMilliseconds(oneDay) == 86400000;
    
  }

  method TestSequenceAggregation() {
    var d_1 := Duration.Duration(0, 500);
    //var d_2 := Duration.Duration(1, 0);
    var d_3 := Duration.Duration(1, 500);
    
    var durations := [d_1, d_3];
    var minD := Duration.MinSeq(durations);
    var maxD := Duration.MaxSeq(durations);
    
   // assert minD == d_3;
   // assert maxD == d_1;
  }

  method TestEdgeCases() {
    var d5 := Duration.FromMilliseconds(1000);
    var d6 := Duration.FromMilliseconds(999);
    
    assert Duration.Less(d6, d5);
    assert !Duration.Less(d5, d6);
    assert Duration.Compare(d5, d5) == 0;
    assert Duration.Compare(d5, d6) == 1;
    assert Duration.Compare(d6, d5) == -1;

  }
  
  method TestEpochDifference() {
    var e1: uint32 := 5000;
    var e2: uint32 := 8000;
    var dd := Duration.EpochDifference(e1, e2);
    assert Duration.ToTotalMilliseconds(dd) == 3000;
  }

  method TestNormalization() {
    var d8 := Duration.FromMilliseconds(2500);
    assert Duration.GetSeconds(d8) == 2;
    assert Duration.GetMilliseconds(d8) == 500;

  }

  method TestLessOrEqual() {
    var d1 := Duration.FromSeconds(5);
    var d2 := Duration.FromSeconds(10);
    
    assert Duration.LessOrEqual(d1, d2);
    assert Duration.LessOrEqual(d1, d1);
    assert !Duration.LessOrEqual(d2, d1);
  }

  method TestStringConversion() {
    var d := Duration.Duration(3665, 500);  // 1H1M5.500S
    var str := Duration.ToString(d);
    assert str[0] == 'P';
    assert str[1] == 'T';
  }

  method Main() {
    TestOfParseString();
    TestBasicCreation();
    TestComparison();
    TestArithmetic();
    TestScalingAndDivision();
    TestMinMax();
    TestUnitConversions();
    TestSequenceAggregation();
    TestEdgeCases();
    TestEpochDifference();
    TestNormalization();
    TestLessOrEqual();
    TestStringConversion();
  }
}
