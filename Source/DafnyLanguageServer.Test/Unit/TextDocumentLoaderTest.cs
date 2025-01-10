using Microsoft.Dafny.LanguageServer.Workspace;
using Moq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using DafnyCore.Test;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit {
  public class TextDocumentLoaderTest {
    private readonly TextWriter output;

    private Mock<IFileSystem> fileSystem;
    private Mock<IDafnyParser> parser;
    private Mock<ISymbolResolver> symbolResolver;
    private TextDocumentLoader textDocumentLoader;
    private Mock<ILogger<ITextDocumentLoader>> logger;

    public TextDocumentLoaderTest(ITestOutputHelper output) {
      this.output = new WriterFromOutputHelper(output);
      parser = new();
      symbolResolver = new();
      fileSystem = new();
      logger = new Mock<ILogger<ITextDocumentLoader>>();
      textDocumentLoader = new TextDocumentLoader(
        logger.Object,
        parser.Object,
        symbolResolver.Object
      );
    }

    private static VersionedTextDocumentIdentifier CreateTestDocumentId() {
      return new VersionedTextDocumentIdentifier() {
        Uri = DocumentUri.Parse("untitled:untitled1"),
        Version = 1,
      };
    }

    [Fact]
    public async Task LoadReturnsCanceledTaskIfOperationIsCanceled() {
      var source = new CancellationTokenSource();
      parser.Setup(p => p.Parse(
          It.IsAny<Compilation>(),
          It.IsAny<CancellationToken>())).Callback(() => source.Cancel())
        .Throws<TaskCanceledException>();
      var task = textDocumentLoader.ParseAsync(GetCompilation(), source.Token);
      try {
        await task;
        Assert.Fail("document load was not cancelled");
      } catch (Exception e) {
        Assert.IsType<TaskCanceledException>(e);
        Assert.True(task.IsCanceled);
        Assert.False(task.IsFaulted);
      }
    }

    private Compilation GetCompilation() {
      var versionedTextDocumentIdentifier = CreateTestDocumentId();
      var uri = versionedTextDocumentIdentifier.Uri.ToUri();
      var fs = new InMemoryFileSystem(ImmutableDictionary<Uri, string>.Empty.Add(uri, ""));
      var file = DafnyFile.HandleDafnyFile(fs, new ErrorReporterSink(DafnyOptions.Default), DafnyOptions.Default, uri, Token.NoToken, false);
      var input = new CompilationInput(DafnyOptions.Default, 0, ProjectManagerDatabase.ImplicitProject(uri));
      var engine = new ExecutionEngine(DafnyOptions.Default, new VerificationResultCache(),
        CustomStackSizePoolTaskScheduler.Create(0, 0));
      var compilation = new Compilation(new Mock<ILogger<Compilation>>().Object, new Mock<IFileSystem>().Object, textDocumentLoader,
        new Mock<IProgramVerifier>().Object, engine, input);
      compilation.RootFiles = Task.FromResult<IReadOnlyList<DafnyFile>>(new[] { file });
      return compilation;
    }

    [Fact]
    public async Task LoadReturnsFaultedTaskIfAnyExceptionOccured() {
      parser.Setup(p => p.Parse(It.IsAny<Compilation>(),
          It.IsAny<CancellationToken>()))
        .Throws<InvalidOperationException>();
      var task = textDocumentLoader.ParseAsync(GetCompilation(), default);
      try {
        await task;
        Assert.Fail("document load did not fail");
      } catch (Exception e) {
        Assert.IsType<InvalidOperationException>(e);
        Assert.False(task.IsCanceled);
        Assert.True(task.IsFaulted);
      }
    }
  }
}
