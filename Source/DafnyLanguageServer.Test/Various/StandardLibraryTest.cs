using System;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class StandardLibraryTest : ClientBasedLanguageServerTest {
  [Fact]
  public async Task CanUseWrappers() {
    var source = @"
import opened Std.Wrappers

const triggerSemicolonWarning := 3;

method Foo() returns (s: Option<int>) { 
  return Some(3); 
}".TrimStart();

    var projectSource = @"
[options]
warn-deprecation = true
standard-libraries = true";

    var withoutStandardLibraries = CreateAndOpenTestDocument(source);
    var diagnostics1 = await GetLastDiagnostics(withoutStandardLibraries, DiagnosticSeverity.Error);
    Assert.Single(diagnostics1);

    var directory = Path.GetTempFileName();
    CreateAndOpenTestDocument(projectSource, Path.Combine(directory, DafnyProject.FileName));
    var document = CreateAndOpenTestDocument(source, Path.Combine(directory, "document.dfy"));
    var diagnostics2 = await GetLastDiagnostics(document);
    Assert.Single(diagnostics2);
    Assert.Equal(DiagnosticSeverity.Warning, diagnostics2[0].Severity);
  }

  [Fact]
  public async Task GotoDefinition() {
    var source = @"
import opened Std.Wrappers

method Foo() returns (s: ><Option<int>) { 
  return Some(3); 
}".TrimStart();

    var projectSource = @"
[options]
standard-libraries = true";

    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);
    await File.WriteAllTextAsync(Path.Combine(directory, DafnyProject.FileName), projectSource);

    MarkupTestFile.GetPositionsAndNamedRanges(source, out var cleanSource,
      out var positions, out var ranges);

    var filePath = Path.Combine(directory, "StandardLibraryGotoDefinition.dfy");
    var documentItem = CreateAndOpenTestDocument(cleanSource, filePath);
    await AssertNoDiagnosticsAreComing(CancellationToken);
    var result = await RequestDefinition(documentItem, positions[0]);
    Assert.Equal(new Uri("dafny:DafnyStandardLibraries.dfy"), result.Single().Location.Uri);
  }

  public StandardLibraryTest(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information) : base(output, dafnyLogLevel) {
  }
}