include "Statistics.dfy"

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
}