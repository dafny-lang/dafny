using System;
using System.Collections.Generic;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Server;
using Xunit;
using LanguageServerExtensions = Microsoft.Dafny.LanguageServer.Workspace.LanguageServerExtensions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class ExceptionTests : ClientBasedLanguageServerTest {

  public bool CrashOnPrepareVerification { get; set; }
  public bool CrashOnLoad { get; set; }

  protected override IServiceCollection ServerOptionsAction(LanguageServerOptions serverOptions) {
    return serverOptions.Services
      .AddSingleton<ITextDocumentLoader>(serviceProvider => new CrashingLoader(this,
        LanguageServerExtensions.CreateTextDocumentLoader(serviceProvider)))
      .AddSingleton<IProgramVerifier>(serviceProvider => new CrashingVerifier(this,
        new DafnyProgramVerifier(
          serviceProvider.GetRequiredService<ILogger<DafnyProgramVerifier>>(),
          serviceProvider.GetRequiredService<DafnyOptions>())
    ));
  }

  [Fact]
  public async Task LoadCrashOnOpenRecovery() {
    var source = @"method Foo() { assert true; }";

    CrashOnLoad = true;
    var documentItem = CreateTestDocument(source);
    client.OpenDocument(documentItem);
    var crashDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(crashDiagnostics);
    Assert.Equal(new Range(0, 0, 0, 1), crashDiagnostics[0].Range);
    Assert.True(crashDiagnostics[0].Message.Contains("internal error"), crashDiagnostics[0].Message);
    CrashOnLoad = false;
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), " ");
    var recoveredDiagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.Empty(recoveredDiagnostics);
  }

  [Fact]
  public async Task LoadCrashOnChangeRecover() {
    var source = @"method Foo() { assert true; }";

    var documentItem = CreateTestDocument(source);
    client.OpenDocument(documentItem);
    var openDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Empty(openDiagnostics);
    CrashOnLoad = true;
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), " ");
    var crashDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(crashDiagnostics);
    Assert.True(crashDiagnostics[0].Message.Contains("internal error"), crashDiagnostics[0].Message);
    CrashOnLoad = false;
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), " ");
    var recoveredDiagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.Empty(recoveredDiagnostics);
  }

  [Fact]
  public async Task PrepareVerificationCrashRecover() {
    var source = @"method Foo() { assert false; }";

    CrashOnPrepareVerification = true;
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Empty(resolutionDiagnostics);
    var translationCrashDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(translationCrashDiagnostics);
    Assert.True(translationCrashDiagnostics[0].Message.Contains("internal error"), translationCrashDiagnostics[0].Message);
    CrashOnPrepareVerification = false;
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), " ");
    var recoveredDiagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.Single(recoveredDiagnostics);
    Assert.True(recoveredDiagnostics[0].Message.Contains("might not"), recoveredDiagnostics[0].Message);
  }

  class CrashingVerifier : IProgramVerifier {
    private readonly ExceptionTests tests;
    private readonly IProgramVerifier verifier;

    public CrashingVerifier(ExceptionTests tests, IProgramVerifier verifier) {
      this.tests = tests;
      this.verifier = verifier;
    }

    public Task<IReadOnlyList<IImplementationTask>> GetVerificationTasksAsync(DocumentAfterResolution document, CancellationToken cancellationToken) {

      if (tests.CrashOnPrepareVerification) {
        throw new Exception("crash");
      }
      return verifier.GetVerificationTasksAsync(document, cancellationToken);
    }

    public void Dispose() {
      verifier?.Dispose();
    }
  }

  class CrashingLoader : ITextDocumentLoader {
    private readonly ExceptionTests tests;
    private readonly ITextDocumentLoader loader;

    public CrashingLoader(ExceptionTests tests, ITextDocumentLoader loader) {
      this.tests = tests;
      this.loader = loader;
    }

    public IdeState CreateUnloaded(DocumentTextBuffer textDocument, CancellationToken cancellationToken) {
      return loader.CreateUnloaded(textDocument, cancellationToken);
    }

    public Task<DocumentAfterParsing> LoadAsync(DafnyOptions options, DocumentTextBuffer textDocument,
      CancellationToken cancellationToken) {
      if (tests.CrashOnLoad) {
        throw new IOException("crash");
      }
      return loader.LoadAsync(options, textDocument, cancellationToken);
    }
  }
}
