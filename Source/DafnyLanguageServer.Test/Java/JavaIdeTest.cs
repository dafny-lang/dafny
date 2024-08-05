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
  
  [Fact]
  public async Task GotoDefinitionJava() {
    var source = @"
class Div {
  int Foo(int [>x<]) {
    return 3 / ><x;
  }
}".TrimStart();
    await AssertPositionsLineUpWithRanges(source, "GotoDefinitionJava.vjava");
  }
  
  [Fact]
  public async Task SafeDivision() {
    var input = @"
class Div {
  int Foo(int x) {
    if (x != 0) {
      return 3 / x;
    }
    return 0;
  }
}".TrimStart(); 
    var document = CreateAndOpenTestDocument(input, "Division.vjava");
    await AssertNoDiagnosticsAreComing(CancellationToken, document);
  }

  public JavaIdeTest(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information) : base(output, dafnyLogLevel)
  {
  }
}