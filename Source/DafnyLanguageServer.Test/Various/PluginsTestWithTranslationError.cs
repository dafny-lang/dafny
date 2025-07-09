using System.Linq;
using System.Threading.Tasks;
using System.Threading;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using XunitAssertMessages;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class PluginsTestWithTranslationError : PluginsTestBase {

  protected override string LibraryName =>
    "PluginsTestTranslationError";

  protected override string[] CommandLineArgument =>
    [$@"{LibraryPath},""because\\ \""whatever"""];

  [Fact]
  public async Task EnsureTranslationErrorsAreReportedEvenWithoutResolutionErrors() {
    // This code will run with the plugin from PluginsAdvancedTest, but that plugin won't throw an exception on the code below.
    var documentItem = CreateTestDocument("function test(): nat { -1 }");// No resolution error
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await GetLastDiagnostics(documentItem);
    AssertM.Equal(2, diagnostics.Length, LibraryPath + " did not return two errors.");
    Assert.Equal("Translation error that should appear in the code", diagnostics[0].Message);
  }

  public PluginsTestWithTranslationError(ITestOutputHelper output) : base(output) {
  }
}
