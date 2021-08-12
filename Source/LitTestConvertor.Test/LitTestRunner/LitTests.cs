using DafnyDriver.Test.XUnitExtensions;
using Xunit;

namespace LitTestConvertor.Test
{
  public class LitTestRunner
  {
    [Theory]
    [LitTestData]
    public void LitTest(CLITestCase testCase) {
      testCase.Run();
    }
  }
}