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
  function F(): int
}

module B refines A {

  lemma Test()
    ensures false
  {
  }

  function F(): int
    ensures false { 3 }

}".TrimStart();
    var document = await CreateOpenAndWaitForResolve(source);
    var diagnostics = await GetLastDiagnostics(document, DiagnosticSeverity.Error);
    Assert.Equal(2, diagnostics.Length);
  }

  public RefinementTests(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information) : base(output, dafnyLogLevel) {
  }
}