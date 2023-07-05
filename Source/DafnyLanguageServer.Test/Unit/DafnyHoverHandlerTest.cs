using Microsoft.Dafny.LanguageServer.Handlers;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit;

public class DafnyHoverHandlerTest {
  [Fact]
  public void FormatResourceUnitTest() {
    void OneTest(string expected, long input) {
      Assert.Equal(expected, DafnyHoverHandler.FormatResourceCount(input));
    }

    OneTest("4 RU", 4);
    OneTest("67 RU", 67);
    OneTest("872 RU", 872);
    OneTest("8.72K RU", 8720);
    OneTest("87.2K RU", 87200);
    OneTest("872K RU", 872000);
    OneTest("8.72M RU", 8720000);
    OneTest("87.2M RU", 87200000);
    OneTest("872M RU", 872000000);
    OneTest("872G RU", 872000000000);
    OneTest("872T RU", 872000000000000);
    OneTest("8720T RU", 8724000000000000);

    // Rounds
    OneTest("8.72K RU", 8724);
    OneTest("8.73K RU", 8725);
    OneTest("8.73K RU", 8726);
    OneTest("87.2K RU", 87245);
    OneTest("87.3K RU", 87250);
    OneTest("87.3K RU", 87255);

    // Zeros should not be trimmed
    OneTest("8.70K RU", 8699);
    OneTest("8.70K RU", 8701);
    OneTest("8.00K RU", 7998);
    OneTest("8.00K RU", 8001);
    OneTest("87.0K RU", 87023);
    OneTest("87.0K RU", 86998);
  }
}