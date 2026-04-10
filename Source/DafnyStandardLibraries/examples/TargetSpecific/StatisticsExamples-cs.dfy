
module TestStatistics {
  import opened Std.Statistics
  import opened Helpers


  method {:test} TestSum() {
    AssertAndExpect(Sum([1.0, 2.0, 3.0, 4.0, 5.0]) == 15.0);
    AssertAndExpect(Sum([1.5, 2.5, 3.5]) == 7.5);
    AssertAndExpect(Sum([100.0]) == 100.0);
    AssertAndExpect(Sum([-10.0, 0.0, 10.0, 20.0]) == 20.0);
    AssertAndExpect(Sum([]) == 0.0);
  }

  method {:test} TestMean() {
    AssertAndExpect(Mean([1.0, 2.0, 3.0, 4.0, 5.0]) == 3.0);
    AssertAndExpect(Mean([1.5, 2.5, 3.5]) == 2.5);
    AssertAndExpect(Mean([100.0]) == 100.0);
    AssertAndExpect(Mean([-10.0, 0.0, 10.0, 20.0]) == 5.0);
  }

  @ResourceLimit("1e7")
  method {:test} TestVariance_DataSet1() {
    var data := [1.0, 2.0, 3.0, 4.0, 5.0];
    AssertAndExpect(VariancePopulation(data) == 2.0);
    AssertAndExpect(VarianceSample(data) == 2.5);
  }

  @ResourceLimit("1e7")
  method {:test} TestVariance_DataSet2() {
    var data2 := [6.0, 7.0, 8.0, 9.0, 10.0];
    AssertAndExpect(VariancePopulation(data2) == 2.0);
    AssertAndExpect(VarianceSample(data2) == 2.5);
  }

  @ResourceLimit("1e7")
  method {:test} TestVariance_DataSet3_Decimals() {
    // Example with decimals
    var data3 := [1.5, 2.5, 3.5, 4.5, 5.5];
    AssertAndExpect(VariancePopulation(data3) == 2.0);
    AssertAndExpect(VarianceSample(data3) == 2.5);
  }

  method {:test} TestStandardDeviation_DataSet1() {
    var eps := 0.000001;
    var data := [1.0, 2.0, 3.0, 4.0, 5.0];
    expect AreNear(StdDevPopulation(data) * StdDevPopulation(data), 2.0, eps);
    expect AreNear(StdDevSample(data) * StdDevSample(data), 2.5, eps);
  }

  method {:test} TestStandardDeviation_DataSet2() {
    var eps := 0.000001;
    var data2 := [6.0, 7.0, 8.0, 9.0, 10.0];
    expect AreNear(StdDevPopulation(data2) * StdDevPopulation(data2), 2.0, eps);
    expect AreNear(StdDevSample(data2) * StdDevSample(data2), 2.5, eps);
  }

  method {:test} TestStandardDeviation_DataSet3_Boundary() {
    var eps := 0.000001;
    var data3 := [1.0, 3.0];
    expect AreNear(StdDevPopulation(data3) * StdDevPopulation(data3), 1.0, eps);
    expect AreNear(StdDevSample(data3) * StdDevSample(data3), 2.0, eps);
  }

  // Testcase for median in odd case
  method {:test} {:rlimit 50000} Test_Median_Odd_Case() {
    AssertAndExpect(Median([3.0, 1.0, 2.0]) == 2.0);
  }

  // Testcase for median in even case
  method {:test} {:rlimit 1000000} Test_Median_Even_Case() {
    AssertAndExpect(Median([4.0, 2.0, 3.0, 1.0]) == (2.0 + 3.0) / 2.0);
  }

  // Testcase for evaluating median for a sequence with single element
  method {:test} Test_Median_Single_Element_Case() {
    AssertAndExpect(Median([42.0]) == 42.0);
  }

  // Testcase for checking already sorted case in median for odd elements
  method {:test} Test_Median_Odd_Case_Sorted_Sequence() {
    AssertAndExpect(Median([1.0, 2.0, 3.0]) == 2.0);
  }

  // Testcase for checking already sorted case in median for even elements
  method {:test} {:rlimit 500000} Test_Median_Even_Case_Sorted_Sequence() {
    AssertAndExpect(Median([1.0, 2.0, 3.0, 4.0]) == (2.0 + 3.0) / 2.0);
  }

  // Testcase for checking mode calculation
  method {:test} Test_Mode() {
    expect Mode([1.0, 2.0, 2.0, 3.0]) == 2.0;
  }

  // Testcase for checking mode with multiple occurences for multiple elements
  method {:test} Test_Mode_Multiple() {
    expect Mode([5.0, 5.0, 7.0, 7.0, 7.0, 9.0]) == 7.0;
  }

  // Testcase for checking mode for a single element sequence
  method {:test} Test_Mode_Single() {
    expect Mode([42.0]) == 42.0;
  }

  // Testcase for checking mode for equal occurences for 2 elements
  method {:test} Test_Mode_Equal() {
    expect Mode([ 6.0, 6.0, 4.0, 4.0]) == 6.0;
  }

  // Testcase for range with multiple elements
  method {:test}  {:rlimit 50000} Test_Range() {
    AssertAndExpect(Range([1.0, 3.0, 5.0]) == 4.0);
  }

  // Testcase for range with single element
  method {:test} Test_Range_Single_Element() {
    AssertAndExpect(Range([42.0]) == 0.0);
  }

  // Testcase for range with  sorted sequence in increasing order
  method {:test}  {:rlimit 50000} Test_Range_Sorted_Sequence() {
    AssertAndExpect(Range([1.0, 2.0, 3.0, 4.0]) == 3.0);
  }

  // Testcase for range with sorted sequence in descending order
  method {:test}  {:rlimit 50000} Test_Range_Descending_Sequence() {
    AssertAndExpect(Range([9.0, 7.0, 5.0, 3.0]) == 6.0);
  }
}