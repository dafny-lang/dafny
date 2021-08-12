using System.Linq;
using DafnyDriver.Test.XUnitExtensions;
using Xunit;

namespace DafnyDriver.Test {
  
  public static class DafnyTests {

    [ParallelTheory]
    [DafnyTestData]
    public static void Test(CLITestCase testCase) {
      testCase.Run();
    }
  }
}