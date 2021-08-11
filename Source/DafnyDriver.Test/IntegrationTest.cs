using System.Linq;
using DafnyDriver.Test.XUnitExtensions;
using Xunit;

namespace DafnyDriver.Test {
  
  public static class DafnyTests {

    // [Fact]
    // public static void DafnyTestDataDiscovererDiscoversAtLeastOneTest() {
    //   // This test is much easier to debug than the main parameterized test
    //   // if the discoverer is not working correctly
    //   var discoverer = new DafnyTestYamlDataDiscoverer();
    //   var testMethod = typeof(DafnyTests).GetMethod(nameof(Test));
    //   var testData = discoverer.GetData(testMethod, false, ).ToList();
    //   Assert.True(testData.Any());
    // }

    [ParallelTheory]
    [DafnyTestData]
    public static void Test(CLITestCase testCase) {
      testCase.Run();
    }
  }
}