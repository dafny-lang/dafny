using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Moq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using IntervalTree;
using JetBrains.Annotations;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit {
  [TestClass]
  public class DocumentDatabaseTest {
    private Mock<ITextDocumentLoader> textDocumentLoader;
    private DocumentDatabase documentDatabase;
    private Mock<MockedLogger> documentDatabaseLogger;
    private MockedOptions options;
    private Mock<TextChangeProcessor> textChangeProcessor;
    private Mock<IRelocator> relocator;

    public abstract class MockedLogger : ILogger<DocumentDatabase> {
      public abstract void Log<TState>(LogLevel logLevel, EventId eventId, TState state, Exception exception, Func<TState, Exception, string> formatter);
      public abstract bool IsEnabled(LogLevel logLevel);
      public abstract IDisposable BeginScope<TState>(TState state);
    }

    public class MockedOptions : IOptions<DocumentOptions> {
      public DocumentOptions Value => new DocumentOptions() {
        ProverOptions = ""
      };
    }

    [TestInitialize]
    public void SetUp() {
      DafnyOptions.Install(new DafnyOptions());
      textChangeProcessor = new Mock<TextChangeProcessor>();
      relocator = new Mock<IRelocator>();
      documentDatabaseLogger = new Mock<MockedLogger>();
      textDocumentLoader = new Mock<ITextDocumentLoader>();
      options = new MockedOptions();
      documentDatabase = new DocumentDatabase(documentDatabaseLogger.Object,
        options,
        textDocumentLoader.Object,
        textChangeProcessor.Object,
        relocator.Object);
    }

    private static DocumentTextBuffer CreateTestDocument() {
      return new DocumentTextBuffer(0) {
        LanguageId = "dafny",
        Version = 1,
        Text = "",
        Uri = "untitled:Untitled-1"
      };
    }

    class MockedReporter : BatchErrorReporter {
      public List<string> Errors => AllMessages.GetValueOrDefault(ErrorLevel.Error, new List<ErrorMessage>())
        .Select(errorMessage => errorMessage.message).ToList();
    }

    [TestMethod]
    public async Task LoadReturnsCanceledTaskIfOperationIsCanceled() {
      var source = new CancellationTokenSource();
      var reporter = new MockedReporter();
      var testDocument = CreateTestDocument();
      var dafnyDocument = GetMockedDafnyDocument(reporter, testDocument);
      Task<DafnyDocument> documentTask = Task.FromResult(
        dafnyDocument);
      textDocumentLoader.Setup(t => t.PrepareVerificationTasksAsync(dafnyDocument, source.Token))
        .ThrowsAsync(new ArgumentException());
      var result = await documentDatabase.LoadVerificationTasksAsync(documentTask, source.Token);
      Assert.AreEqual(1, reporter.Count(ErrorLevel.Error));
      Assert.AreEqual(0, reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error));
      Assert.IsTrue(reporter.Errors[0].Contains("Dafny encountered an error during 'translation'"));
      Assert.IsFalse(result.CanDoVerification);
    }

    private static DafnyDocument GetMockedDafnyDocument(MockedReporter reporter, DocumentTextBuffer testDocument) {
      var moduleDefinition = new Mock<DefaultModuleDecl>();
      var moduleDecl = new Mock<LiteralModuleDecl>(moduleDefinition.Object, null);
      var program = new Mock<Microsoft.Dafny.Program>(
        "dummy", moduleDecl.Object, new Mock<BuiltIns>().Object, reporter);
      var intervalTree = new Mock<IIntervalTree<Position, ILocalizableSymbol>>();
      intervalTree.Setup(t => t.Query(new Position(0, 0))).Returns<ILocalizableSymbol>(null);
      var symbolTable = new Mock<SymbolTable>(
        null, null, null, null, intervalTree.Object, null
      );
      var dafnyDocument = new DafnyDocument(testDocument,
        new List<Diagnostic>(),
        true,
        null,
        new List<Counterexample>(),
        new List<Diagnostic>(),
        program.Object,
        symbolTable.Object,
        null
      );
      return dafnyDocument;
    }
  }
}
