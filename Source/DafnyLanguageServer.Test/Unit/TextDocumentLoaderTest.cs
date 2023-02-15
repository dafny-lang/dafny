using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Moq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit {
  [TestClass]
  public class TextDocumentLoaderTest {
    private Mock<IDafnyParser> parser;
    private Mock<ISymbolResolver> symbolResolver;
    private Mock<ISymbolTableFactory> symbolTableFactory;
    private Mock<IGhostStateDiagnosticCollector> ghostStateDiagnosticCollector;
    private Mock<ICompilationStatusNotificationPublisher> notificationPublisher;
    private TextDocumentLoader textDocumentLoader;
    private Mock<ILoggerFactory> logger;
    private Mock<INotificationPublisher> diagnosticPublisher;

    [TestInitialize]
    public void SetUp() {
      parser = new();
      symbolResolver = new();
      symbolTableFactory = new();
      ghostStateDiagnosticCollector = new();
      notificationPublisher = new();
      logger = new Mock<ILoggerFactory>();
      diagnosticPublisher = new Mock<INotificationPublisher>();
      textDocumentLoader = TextDocumentLoader.Create(
        DafnyOptions.Create(),
        parser.Object,
        symbolResolver.Object,
        symbolTableFactory.Object,
        ghostStateDiagnosticCollector.Object,
        notificationPublisher.Object,
        logger.Object,
        diagnosticPublisher.Object
      );
    }

    private static DocumentTextBuffer CreateTestDocument() {
      return new DocumentTextBuffer(new TextDocumentItem() {
        LanguageId = "dafny",
        Version = 1,
        Text = ""
      });
    }

    [TestMethod]
    public async Task LoadReturnsCanceledTaskIfOperationIsCanceled() {
      var source = new CancellationTokenSource();
      parser.Setup(p => p.Parse(It.IsAny<TextDocumentItem>(), It.IsAny<ErrorReporter>(), It.IsAny<CancellationToken>())).Callback(() => source.Cancel())
        .Throws<TaskCanceledException>();
      var task = textDocumentLoader.LoadAsync(CreateTestDocument(), source.Token);
      try {
        await task;
        Assert.Fail("document load was not cancelled");
      } catch (Exception e) {
        Assert.IsInstanceOfType(e, typeof(OperationCanceledException));
        Assert.IsTrue(task.IsCanceled);
        Assert.IsFalse(task.IsFaulted);
      }
    }

    [TestMethod]
    public async Task LoadReturnsFaultedTaskIfAnyExceptionOccured() {
      parser.Setup(p => p.Parse(It.IsAny<TextDocumentItem>(), It.IsAny<ErrorReporter>(), It.IsAny<CancellationToken>()))
        .Throws<InvalidOperationException>();
      var task = textDocumentLoader.LoadAsync(CreateTestDocument(), default);
      try {
        await task;
        Assert.Fail("document load did not fail");
      } catch (Exception e) {
        Assert.IsNotInstanceOfType(e, typeof(OperationCanceledException));
        Assert.IsFalse(task.IsCanceled);
        Assert.IsTrue(task.IsFaulted);
      }
    }
  }
}
