using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Refinement; 

public class RefinementTests : ClientBasedLanguageServerTest {
  [Fact]
  public async Task RefinedLemmaNewEnsuresIsVerified() {
    var source = @"
module A {

  lemma Test()

}

module B refines A {

  lemma Test()
    ensures false
  {
  }

}".TrimStart();
    var document = await CreateOpenAndWaitForResolve(source);
    var diagnostics = await GetLastDiagnostics(document);
    Assert.NotEmpty(diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error));
  }

  public RefinementTests(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information) : base(output, dafnyLogLevel) {
  }
}