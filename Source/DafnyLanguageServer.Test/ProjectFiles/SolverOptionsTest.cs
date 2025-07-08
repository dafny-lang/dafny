using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using Moq;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.ProjectFiles;

public class SolverOptionsTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task DisableNonLinearArithmeticIsUsed() {
    var projectFileSource = @"
[options]
disable-nonlinear-arithmetic = true".TrimStart();

    var source = @"
lemma Test(a: real, b: real)
  requires b != 0.0
  ensures a / b == 1.0 / b * a
{}".TrimStart();

    var directory = Path.GetRandomFileName();
    CreateAndOpenTestDocument(projectFileSource, Path.Combine(directory, DafnyProject.FileName));
    var sourceDocument =
      CreateAndOpenTestDocument(source, Path.Combine(directory, "DisableNonLinearArithmeticIsUsed.dfy"));
    var diagnostics = await GetLastDiagnostics(sourceDocument);
    Assert.Single(diagnostics);
    Assert.Contains("a postcondition", diagnostics.First().Message);
  }

  public SolverOptionsTest(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information) : base(output, dafnyLogLevel) {
  }
}