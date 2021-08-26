using DafnyDriver.Test.XUnitExtensions;
using Xunit;

namespace LitTestConvertor.Test.LitTestRunner
{
  public class LitTests
  {
    [Theory]
    [LitTestData]
    public void LitTest(CLITestCase testCase) {
      testCase.Run();
    }
  }
}