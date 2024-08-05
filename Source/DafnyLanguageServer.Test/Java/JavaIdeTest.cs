using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Java;

public class JavaIdeTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task Division() {
    var input = @"
class Div {
  int Foo(int x) {
    return 3 / x;
  }
}".TrimStart(); 
    var document = CreateAndOpenTestDocument(input, "Division.vjava");
    var diagnostics = await GetLastDiagnostics(document);
    Assert.Single(diagnostics);
    Assert.Equal("possible division by zero", diagnostics[0].Message);
  }

  public JavaIdeTest(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information) : base(output, dafnyLogLevel)
  {
  }
}