using System;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Server;
using LanguageServerExtensions = Microsoft.Dafny.LanguageServer.Workspace.LanguageServerExtensions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[TestClass]
public class ExceptionTests : ClientBasedLanguageServerTest {

  private CrashingLoader loader;

  protected override IServiceCollection ServerOptionsAction(LanguageServerOptions serverOptions) {
    return serverOptions.Services.AddSingleton<ITextDocumentLoader>(serviceProvider => {
      loader = new CrashingLoader(
        LanguageServerExtensions.CreateTextDocumentLoader(serviceProvider)
      );
      return loader;
    });
  }

  [TestMethod]
  public async Task LoadCrashOnOpenRecovery() {
    var source = @"method Foo() { assert true; }";

    loader.CrashOnLoad = true;
    var documentItem = CreateTestDocument(source);
    client.OpenDocument(documentItem);
    var crashDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, crashDiagnostics.Length);
    Assert.IsTrue(crashDiagnostics[0].Message.Contains("internal error"), crashDiagnostics[0].Message);
    loader.CrashOnLoad = false;
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), " ");
    var recoveredDiagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.AreEqual(0, recoveredDiagnostics.Length);
  }

  [TestMethod]
  public async Task LoadCrashOnChangeRecover() {
    var source = @"method Foo() { assert true; }";

    var documentItem = CreateTestDocument(source);
    client.OpenDocument(documentItem);
    var openDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(0, openDiagnostics.Length);
    loader.CrashOnLoad = true;
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), " ");
    var crashDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, crashDiagnostics.Length);
    Assert.IsTrue(crashDiagnostics[0].Message.Contains("internal error"), crashDiagnostics[0].Message);
    loader.CrashOnLoad = false;
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), " ");
    var recoveredDiagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.AreEqual(0, recoveredDiagnostics.Length);
  }

  [TestMethod]
  public async Task PrepareVerificationCrashRecover() {
    var source = @"method Foo() { assert false; }";

    loader.CrashOnPrepareVerification = true;
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(0, resolutionDiagnostics.Length);
    var translationCrashDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, translationCrashDiagnostics.Length);
    Assert.IsTrue(translationCrashDiagnostics[0].Message.Contains("internal error"), translationCrashDiagnostics[0].Message);
    loader.CrashOnPrepareVerification = false;
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), " ");
    var recoveredDiagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.AreEqual(1, recoveredDiagnostics.Length);
    Assert.IsTrue(recoveredDiagnostics[0].Message.Contains("might not"), recoveredDiagnostics[0].Message);
  }

  class CrashingLoader : ITextDocumentLoader {
    private readonly ITextDocumentLoader loader;
    public bool CrashOnPrepareVerification { get; set; }
    public bool CrashOnLoad { get; set; }

    public CrashingLoader(ITextDocumentLoader loader) {
      this.loader = loader;
    }

    public DafnyDocument CreateUnloaded(DocumentTextBuffer textDocument, CancellationToken cancellationToken) {
      return loader.CreateUnloaded(textDocument, cancellationToken);
    }

    public Task<DafnyDocument> LoadAsync(DocumentTextBuffer textDocument, CancellationToken cancellationToken) {
      if (CrashOnLoad) {
        throw new Exception("crash");
      }
      return loader.LoadAsync(textDocument, cancellationToken);
    }

    public Task<DafnyDocument> PrepareVerificationTasksAsync(DafnyDocument loaded, CancellationToken cancellationToken) {
      if (CrashOnPrepareVerification) {
        throw new Exception("crash");
      }
      return loader.PrepareVerificationTasksAsync(loaded, cancellationToken);
    }

    public IObservable<DafnyDocument> VerifyAllTasks(DafnyDocument document, CancellationToken cancellationToken) {
      return loader.VerifyAllTasks(document, cancellationToken);
    }

    public IObservable<DafnyDocument> Verify(DafnyDocument document, IImplementationTask implementationTask, CancellationToken cancellationToken) {
      return loader.Verify(document, implementationTask, cancellationToken);
    }

    public void PublishGutterIcons(DafnyDocument document, bool verificationStarted) {
      loader.PublishGutterIcons(document, verificationStarted);
    }
  }
}