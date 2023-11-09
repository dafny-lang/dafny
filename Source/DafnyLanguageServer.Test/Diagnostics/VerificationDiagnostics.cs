using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

public class VerificationDiagnostics : ClientBasedLanguageServerTest {

  [Fact]
  public async Task ErrorLimitReached() {
    var source = @"
method ErrorLimitReached(x: int) {
  assert x > 0;
  assert x > 1;
  assert x > 2;
  assert x > 3;
  assert x > 4;
  assert x > 5;
  if (*) {
    assert false;
  } else {
    var x := 3 / 2;
  }
}".TrimStart();
    var document = CreateAndOpenTestDocument(source, "ErrorLimitReached.dfy");
    var diagnostics = await GetLastDiagnostics(document);
    Assert.Contains(diagnostics, d => d.Message.Contains("Verification hit error limit"));
  }

  [Fact]
  public async Task ShowImplicitAssertions() {
    await SetUp(o => o.Set(CommonOptionBag.ShowAssertions, CommonOptionBag.AssertionShowMode.Implicit));

    var source = @"
method ImplicitAssertions(x: int) {
  if (*) {
    assert false;
  } else {
    var x := 3 / 2;
  }
}".TrimStart();
    var document = CreateAndOpenTestDocument(source, "ErrorLimitReached.dfy");
    var diagnostics = await GetLastDiagnostics(document, DiagnosticSeverity.Hint);
    Assert.Contains(diagnostics, d => d.Message.Contains("Implicit assertion: non-zero divisor")
                                      && d.Range == new Range(4, 15, 4, 16));
    Assert.DoesNotContain(diagnostics, d => d.Message.Contains("Explicit assertion: assert statement"));
  }

  [Fact]
  public async Task ShowAllAssertions() {
    await SetUp(o => o.Set(CommonOptionBag.ShowAssertions, CommonOptionBag.AssertionShowMode.All));

    var source = @"
method ImplicitAssertions(x: int) {
  if (*) {
    assert false;
  } else {
    var x := 3 / 2;
  }
}".TrimStart();
    var document = CreateAndOpenTestDocument(source, "ErrorLimitReached.dfy");
    var diagnostics = await GetLastDiagnostics(document, DiagnosticSeverity.Hint);
    Assert.Contains(diagnostics, d => d.Message.Contains("Implicit assertion: non-zero divisor"));
    Assert.Contains(diagnostics, d => d.Message.Contains("Explicit assertion: assert statement") && d.Range == new Range(2, 11, 2, 16));
  }

  public VerificationDiagnostics(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information) : base(output, dafnyLogLevel) {
  }
}