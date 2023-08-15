using System.Linq;
using System.Threading.Tasks;
using System.Threading;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Xunit;
using Xunit.Abstractions;
using XunitAssertMessages;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class PluginsTestWithTranslationError : PluginsTestBase {

  protected override string LibraryName =>
    "PluginsTestTranslationError";

  protected override string[] CommandLineArgument =>
    new[] { $@"{LibraryPath},""because\\ \""whatever""" };

  [Fact]
  public async Task EnsureTranslationErrorsAreReportedEvenWithoutResolutionErrors() {
    // This code will run with the plugin from PluginsAdvancedTest, but that plugin won't throw an exception on the code below.
    var documentItem = CreateTestDocument("function test(): nat { -1 }");// No resolution error
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionReport = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(documentItem.Uri, resolutionReport.Uri);
    var verificationReport = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(documentItem.Uri, verificationReport.Uri);
    var diagnostics = verificationReport.Diagnostics.ToArray();
    AssertM.Equal(2, diagnostics.Length, LibraryPath + " did not return two errors.");
    Assert.Equal("Translation error that should appear in the code", diagnostics[0].Message);
  }

  public PluginsTestWithTranslationError(ITestOutputHelper output) : base(output) {
  }
}
