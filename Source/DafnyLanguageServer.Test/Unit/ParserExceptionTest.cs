using System;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using Moq;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Serilog;
using Serilog.Sinks.InMemory;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit {

  public class ParserExceptionTest {
    private static readonly string TestFilePath = "parserException.dfy";
    private const string LanguageId = "dafny";
    private const int MaxTestExecutionTimeMs = 10_000;
    private DafnyLangParser parser;
    private readonly InMemorySink sink;
    private LanguageServerFilesystem fileSystem;

    public ParserExceptionTest(ITestOutputHelper output) {

      sink = InMemorySink.Instance;
      var logger = new LoggerConfiguration().MinimumLevel.Debug()
        .WriteTo.InMemory().CreateLogger();
      var factory = LoggerFactory.Create(b => b.AddSerilog(logger));

      fileSystem = new LanguageServerFilesystem();
      parser = DafnyLangParser.Create(DafnyOptions.Create(new WriterFromOutputHelper(output)),
        fileSystem, Mock.Of<ITelemetryPublisher>(), factory);
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public void DocumentWithParserExceptionDisplaysIt() {
      var source = "function t() { / }";
      var options = new DafnyOptions(DafnyOptions.DefaultImmutableOptions);
      var documentItem = CreateTestDocument(source, TestFilePath);
      var uri = new Uri("file:///" + TestFilePath);
      fileSystem.OpenDocument(documentItem);
      var errorReporter = new ParserExceptionSimulatingErrorReporter(options);
      parser.Parse(new DocumentTextBuffer(documentItem), errorReporter, default);
      Assert.Contains(sink.LogEvents, le => le.MessageTemplate.Text.Contains($"encountered an exception while parsing {uri}"));
      Assert.Equal($"/{TestFilePath}(1,0): Error: [internal error] Parser exception: Simulated parser internal error", errorReporter.LastMessage);
    }

    /// <summary>
    /// An error reporter that throws an exception on the first reported error, to simulate a parser exception.
    /// </summary>
    private class ParserExceptionSimulatingErrorReporter : ErrorReporter {
      private int numberOfErrors;
      public string LastMessage = "";
      public override bool Message(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg) {
        if (level != ErrorLevel.Error) {
          return false;
        }

        numberOfErrors++;
        if (numberOfErrors == 1) {
          throw new InvalidOperationException("Simulated parser internal error");
        }

        LastMessage = ErrorToString(level, tok, msg);
        return true;
      }

      public override int Count(ErrorLevel level) {
        return numberOfErrors;
      }

      public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
        throw new NotImplementedException();
      }

      public ParserExceptionSimulatingErrorReporter(DafnyOptions options) : base(options) {
      }
    }

    private static TextDocumentItem CreateTestDocument(string source, string filePath, int version = 1) {
      return new TextDocumentItem {
        LanguageId = LanguageId,
        Text = source,
        Uri = DocumentUri.FromFileSystemPath(filePath),
        Version = version
      };
    }
  }
}
