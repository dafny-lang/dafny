using System.IO;
using System.Linq;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  public class CloseDocumentTest : ClientBasedLanguageServerTest {

    [Fact]
    public async Task DiagnosticsAreClearedUponCloseWhenUsingProject() {
      var source = "method Foo() { var c: int := true; }";
      var directory = GetFreshTempPath();
      Directory.CreateDirectory(directory);
      await File.WriteAllTextAsync(Path.Combine(directory, DafnyProject.FileName), "");
      var document = CreateAndOpenTestDocument(source, Path.Combine(directory, "DiagnosticsAreClearedUponCloseWhenUsingProject.dfy"));
      var diagnostics = await GetLastDiagnostics(document);
      Assert.Single(diagnostics);
      client.CloseDocument(document);
      var afterCloseDiagnostics = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
      var afterCloseDiagnostics2 = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.Contains(new[] { afterCloseDiagnostics, afterCloseDiagnostics2 },
        d => d.Uri == document.Uri && !d.Diagnostics.Any());
      Directory.Delete(directory, true);
    }

    [Fact]
    public async Task DiagnosticsAreClearedUponClose() {
      var source = "method Foo() { var c: int := true; }";
      var document = CreateAndOpenTestDocument(source);
      var diagnostics = await GetLastDiagnostics(document);
      Assert.Single(diagnostics);
      client.CloseDocument(document);
      var afterCloseDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.Empty(afterCloseDiagnostics);
    }

    [Fact]
    public async Task DocumentIsUnloadedWhenClosed() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source, "DocumentIsUnloadedWhenClosed.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      client.CloseDocument(documentItem);
      for (int attempt = 0; attempt < 50; attempt++) {
        if (!Projects.Managers.Any()) {
          return;
        }

        await Task.Delay(100);
      }
      Assert.Fail("all attempts failed");
    }

    [Fact]
    public async Task DocumentStaysUnloadedWhenClosed() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source, "DocumentStaysUnloadedWhenClosed.dfy");
      client.CloseDocument(documentItem);
      Assert.Null(await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri));
    }

    public CloseDocumentTest(ITestOutputHelper output) : base(output) {
    }
  }
}
