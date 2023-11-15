using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

public class ProjectDiagnosticsTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task LibraryNotFound() {
    var projectFile = @"
[options]
library = [""doesNotExist.dfy""]
".TrimStart();

    var project = CreateAndOpenTestDocument(projectFile, DafnyProject.FileName);
    var diagnostics = await GetLastDiagnostics(project);
    Assert.Contains("msg", diagnostics[0].Message);
  }

  public ProjectDiagnosticsTest(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information)
    : base(output, dafnyLogLevel) {
  }
}