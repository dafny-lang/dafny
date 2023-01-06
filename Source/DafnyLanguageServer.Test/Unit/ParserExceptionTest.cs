using System;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit {

  [TestClass]
  public class ParserExceptionTest {
    private static readonly string TestFilePath = "parserException.dfy";
    private const string LanguageId = "dafny";
    private const int MaxTestExecutionTimeMs = 10_000;
    private DafnyLangParser parser;
    private LastDebugLogger lastDebugLogger;

    [TestInitialize]
    public void SetUp() {
      lastDebugLogger = new LastDebugLogger();
      parser = DafnyLangParser.Create(lastDebugLogger);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public void DocumentWithParserExceptionDisplaysIt() {
      var source = "function t() { / }";
      var documentItem = CreateTestDocument(source, TestFilePath);
      var errorReporter = new ParserExceptionSimulatingErrorReporter();
      parser.Parse(documentItem, errorReporter, default);
      Assert.AreEqual($"encountered an exception while parsing file:///{TestFilePath}", lastDebugLogger.LastDebugMessage);
      Assert.AreEqual($"file:///{TestFilePath}(1,0): Error: [internal error] Parser exception: Simulated parser internal error", errorReporter.LastMessage);
    }

    /// <summary>
    /// An error reporter that throws an exception on the first reported error, to simulate a parser exception.
    /// </summary>
    private class ParserExceptionSimulatingErrorReporter : ErrorReporter {
      private int numberOfErrors;
      public string LastMessage = "";
      public override bool Message(MessageSource source, ErrorLevel level, string errorID, IToken tok, string msg) {
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
        throw new NotImplementedException();
      }

      public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
        throw new NotImplementedException();
      }
    }

    // Helpers and definitions

    /// <summary>
    /// Retains the last debug logged message
    /// </summary>
    private class LastDebugLogger : ILogger<DafnyLangParser> {
      public string LastDebugMessage = "";
      public void Log<TState>(LogLevel logLevel, EventId eventId, TState state, Exception exception, Func<TState, Exception, string> formatter) {
        if (logLevel is LogLevel.Debug) {
          LastDebugMessage = formatter(state, exception);
          return;
        }
        if (logLevel is LogLevel.Trace or LogLevel.Information or LogLevel.Warning) {
          return;
        }
        throw new NotImplementedException();
      }

      public bool IsEnabled(LogLevel logLevel) {
        return true;
      }

      public IDisposable BeginScope<TState>(TState state) {
        throw new NotImplementedException();
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
