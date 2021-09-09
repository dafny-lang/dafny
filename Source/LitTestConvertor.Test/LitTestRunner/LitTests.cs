using Xunit;
using XUnitExtensions;

[assembly: TestCollectionOrderer("XUnitExtensions.TestCollectionShardFilter", "XUnitExtensions")]

namespace LitTestConvertor.Test.LitTestRunner {
  public class LitTests {
    [FileTheory]
    [LitTestData(Extension = ".dfy", InvokeCliDirectly = false)]
    public void LitTest(CLITestCase testCase) {
      testCase.Run();
    }
  }
}