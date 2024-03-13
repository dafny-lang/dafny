using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.ProjectFiles;

public class StandardLibrary : ClientBasedLanguageServerTest {

  [Fact]
  public async Task EditWhenUsingStandardLibrary() {
    var projectFile = @"
[options]
standard-libraries=true
";
    var program = @"
method Foo() ensures false { }
".TrimStart();
    var path = Path.GetRandomFileName();
    var project = CreateAndOpenTestDocument(projectFile, Path.Combine(path, DafnyProject.FileName));
    var document = CreateAndOpenTestDocument(program, Path.Combine(path, "EditWhenUsingStandardLibrary.dfy"));
    var diagnostics1 = await GetLastDiagnostics(document);
    Assert.Single(diagnostics1);
    ApplyChange(ref document, new Range(0, 0, 1, 0), "method Bar() ensures true { }");
    var diagnostics2 = await GetLastDiagnostics(document);
    Assert.Empty(diagnostics2);
  }

  public StandardLibrary(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information) : base(output, dafnyLogLevel) {
  }
}