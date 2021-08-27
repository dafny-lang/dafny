using DafnyDriver.Test.XUnitExtensions;

namespace LitTestConvertor.Test.LitTestRunner
{
  public class LitTests
  {
    [ParallelTheory]
    [LitTestData]
    public void LitTest(CLITestCase testCase) {
      testCase.Run();
    }
  }
}