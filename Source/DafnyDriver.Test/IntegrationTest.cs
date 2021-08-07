using System.Linq;
using Xunit;
using Xunit.Sdk;
using XUnitExtensions;

namespace DafnyDriver.Test {
  
  public class DafnyTests {

    [Fact]
    public static void MetaTest() {
      var discoverer = new DafnyTestYamlDataDiscoverer();
      var testMethod = typeof(DafnyTests).GetMethod(nameof(Test));
      var testData = discoverer.GetData(testMethod, false).ToList();
      Assert.True(testData.Any());
    }

    [ParallelTheory]
    [DafnyTestData(false)]
    public static void Test(DafnyTestCase testCase) {
      testCase.Run();
    }
  }
}