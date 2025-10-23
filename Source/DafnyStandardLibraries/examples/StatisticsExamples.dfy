include "../src/Std/Statistics.dfy"

module TestStatistics {
  import opened Std.Statistics
  // Test cases for the StatisticsLibrary functions

  method {:test} TestSum() {
    assert Sum([1.0, 2.0, 3.0, 4.0, 5.0]) == 15.0;
    assert Sum([1.5, 2.5, 3.5]) == 7.5;
    assert Sum([100.0]) == 100.0;
    assert Sum([-10.0, 0.0, 10.0, 20.0]) == 20.0;
    assert Sum([]) == 0.0;
  }

  method {:test} TestMean() {
    assert Mean([1.0, 2.0, 3.0, 4.0, 5.0]) == 3.0;
    assert Mean([1.5, 2.5, 3.5]) == 2.5;
    assert Mean([100.0]) == 100.0;
    assert Mean([-10.0, 0.0, 10.0, 20.0]) == 5.0;
  }

  method {:test} TestVariance() {
    var data := [1.0, 2.0, 3.0, 4.0, 5.0];
    assert VariancePopulation(data) == 2.0;
    assert VarianceSample(data) == 2.5;

    var data2 := [6.0, 7.0, 8.0, 9.0, 10.0];
    assert VariancePopulation(data2) == 2.0;
    assert VarianceSample(data2) == 2.5;

    // Example with decimals
    var data3 := [1.5, 2.5, 3.5, 4.5, 5.5];
    assert VariancePopulation(data3) == 2.0;
    assert VarianceSample(data3) == 2.5;
  }

  method {:test} TestStandardDeviation() {
    // Use Sqrt spec indirectly: compare (StdDev)^2 to expected variance
    var eps := 0.000001;

    // --- Dataset 1 ---
    var data := [1.0, 2.0, 3.0, 4.0, 5.0];
    assert AreNear(StdDevPopulation(data) * StdDevPopulation(data), 2.0, eps);
    assert AreNear(StdDevSample(data) * StdDevSample(data), 2.5, eps);

    // --- Dataset 2 ---
    var data2 := [6.0, 7.0, 8.0, 9.0, 10.0];
    assert AreNear(StdDevPopulation(data2) * StdDevPopulation(data2), 2.0, eps);
    assert AreNear(StdDevSample(data2) * StdDevSample(data2), 2.5, eps);

    // --- Dataset 3 (Boundary Case) ---
    var data3 := [1.0, 3.0];
    assert AreNear(StdDevPopulation(data3) * StdDevPopulation(data3), 1.0, eps);
    assert AreNear(StdDevSample(data3) * StdDevSample(data3), 2.0, eps);
  }

  // Testcase for median in odd case
  method {:test} Test_Median_Odd_Case() {
    assert Median([3.0, 1.0, 2.0]) == 2.0;
  }

  // Testcase for median in even case
  method {:test} Test_Median_Even_Case() {
    assert Median([4.0, 2.0, 3.0, 1.0]) == (2.0 + 3.0) / 2.0;
  }

  // Testcase for evaluating median for a sequence with single element
  method {:test} Test_Median_Single_Element_Case() {
    assert Median([42.0]) == 42.0;
  }

  // Testcase for checking already sorted case in median for odd elements
  method {:test} Test_Median_Odd_Case_Sorted_Sequence() {
    assert Median([1.0, 2.0, 3.0]) == 2.0;
  }

  // Testcase for checking already sorted case in median for even elements
  method {:test} Test_Median_Even_Case_Sorted_Sequence() {
    assert Median([1.0, 2.0, 3.0, 4.0]) == (2.0 + 3.0) / 2.0;
  }
  // Testcase for checking mode calculation
  method {:test} Test_Mode() {
    assert Mode([1.0, 2.0, 2.0, 3.0]) == 2.0;
  }

  // Testcase for checking mode with multiple occurences for multiple elements
  method {:test} Test_Mode_Multiple() {
    assert Mode([5.0, 5.0, 7.0, 7.0, 7.0, 9.0]) == 7.0;
  }

  // Testcase for checking mode for a single element sequence
  method {:test} Test_Mode_Single() {
    assert Mode([42.0]) == 42.0;
  }

  // Testcase for checking mode for equal occurences for 2 elements
  method {:test} Test_Mode_Equal() {

    assert Mode([4.0, 4.0, 6.0, 6.0]) == 4.0
           || Mode([4.0, 4.0, 6.0, 6.0]) == 6.0;
  }


  // Testcase for range with multiple elements
  method {:test} Test_Range() {
    assert Range([1.0, 3.0, 5.0]) == 4.0;
  }

  // Testcase for range with single element
  method {:test} Test_Range_Single_Element() {
    assert Range([42.0]) == 0.0;
  }

  // Testcase for range with  sorted sequence in increasing order
  method {:test} Test_Range_Sorted_Sequence() {
    assert Range([1.0, 2.0, 3.0, 4.0]) == 3.0;
  }

  // Testcase for range with sorted sequence in descending order
  method {:test} Test_Range_Descending_Sequence() {
    assert Range([9.0, 7.0, 5.0, 3.0]) == 6.0;
  }
}