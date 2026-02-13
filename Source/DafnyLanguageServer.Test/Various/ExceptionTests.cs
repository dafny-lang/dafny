using System;
using System.Collections.Generic;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Server;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class ExceptionTests : ClientBasedLanguageServerTest {

  public bool CrashOnPrepareVerification { get; set; }
  public bool CrashOnLoad { get; set; }

  protected override void ServerOptionsAction(LanguageServerOptions serverOptions) {
    serverOptions.Services
      .AddSingleton<TextDocumentLoader, TextDocumentLoader>()
      .AddSingleton<ITextDocumentLoader>(serviceProvider => new CrashingLoader(this,
        serviceProvider.GetRequiredService<TextDocumentLoader>()))
      .AddSingleton<IProgramVerifier>(serviceProvider => new CrashingVerifier(this,
        new DafnyProgramVerifier(serviceProvider.GetRequiredService<ILogger<DafnyProgramVerifier>>())
    ));
  }

  [Fact]
  public async Task LoadCrashOnOpenRecovery() {
    var source = @"method Foo() { assert true; }";

    CrashOnLoad = true;
    var documentItem = CreateTestDocument(source, "LoadCrashOnOpenRecovery.dfy");
    client.OpenDocument(documentItem);
    var crashDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(crashDiagnostics);
    Assert.Equal(new Range(0, 0, 0, 1), crashDiagnostics[0].Range);
    Assert.True(crashDiagnostics[0].Message.Contains("internal error"), crashDiagnostics[0].Message);
    CrashOnLoad = false;
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), " ");
    var recoveredDiagnostics = await GetLastDiagnostics(documentItem);
    Assert.Empty(recoveredDiagnostics);
  }

  [Fact]
  public async Task LoadCrashOnChangeRecover() {
    var source = @"method Foo() { assert true; }";

    var documentItem = CreateTestDocument(source, "LoadCrashOnChangeRecover.dfy");
    client.OpenDocument(documentItem);
    CrashOnLoad = true;
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), " ");
    var crashDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(crashDiagnostics);
    Assert.True(crashDiagnostics[0].Message.Contains("internal error"), crashDiagnostics[0].Message);
    CrashOnLoad = false;
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), " ");
    var recoveredDiagnostics = await GetLastDiagnostics(documentItem);
    Assert.Empty(recoveredDiagnostics);
  }

  [Fact]
  public async Task PrepareVerificationCrashRecover() {
    var source = @"method Foo() { assert false; }";

    CrashOnPrepareVerification = true;
    var documentItem = CreateTestDocument(source, "PrepareVerificationCrashRecover.dfy");
    client.OpenDocument(documentItem);
    var translationCrashDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(translationCrashDiagnostics);
    Assert.True(translationCrashDiagnostics[0].Message.Contains("internal error"), translationCrashDiagnostics[0].Message);
    CrashOnPrepareVerification = false;
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), " ");
    var recoveredDiagnostics = await GetLastDiagnostics(documentItem);
    Assert.Single(recoveredDiagnostics);
    Assert.True(recoveredDiagnostics[0].Message.Contains("not be proved"), recoveredDiagnostics[0].Message);
  }

  class CrashingVerifier : IProgramVerifier {
    private readonly ExceptionTests tests;
    private readonly IProgramVerifier verifier;

    public CrashingVerifier(ExceptionTests tests, IProgramVerifier verifier) {
      this.tests = tests;
      this.verifier = verifier;
    }

    public Task<IReadOnlyList<IVerificationTask>> GetVerificationTasksAsync(ExecutionEngine engine,
      ResolutionResult resolution, ModuleDefinition moduleDefinition, CancellationToken cancellationToken) {

      if (tests.CrashOnPrepareVerification) {
        throw new TestException("testing crash");
      }
      return verifier.GetVerificationTasksAsync(engine, resolution, moduleDefinition, cancellationToken);
    }
  }

  class TestException : Exception {
    public TestException([CanBeNull] string message) : base(message) {
    }
  }

  class CrashingLoader : ITextDocumentLoader {
    private readonly ExceptionTests tests;
    private readonly TextDocumentLoader loader;

    public CrashingLoader(ExceptionTests tests, TextDocumentLoader loader) {
      this.tests = tests;
      this.loader = loader;
    }

    public Task<ProgramParseResult> ParseAsync(Compilation compilation, CancellationToken cancellationToken) {
      return loader.ParseAsync(compilation, cancellationToken);
    }

    public Task<ResolutionResult> ResolveAsync(Compilation compilation,
      Program program,
      CancellationToken cancellationToken) {
      if (tests.CrashOnLoad) {
        throw new IOException("testing crash");
      }
      return loader.ResolveAsync(compilation, program, cancellationToken);
    }
  }

  public ExceptionTests(ITestOutputHelper output) : base(output) {
  }
}
