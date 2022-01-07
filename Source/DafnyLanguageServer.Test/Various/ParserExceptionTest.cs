using System;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {


  [TestClass]
  public class ParserExceptionTest : DafnyLanguageServerTestBase {
    private static readonly string TestFilePath = "parserException.dfy";

    private const int MaxTestExecutionTimeMs = 10000;

    private DafnyLangParser parser;
    private IDictionary<string, string> configuration;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public class CustomLogger : ILogger<DafnyLangParser> {
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

    public CustomLogger customLogger = new();

    public Task SetUp(IDictionary<string, string> newConfiguration) {
      this.configuration = newConfiguration;
      return Task.Run(() => parser = DafnyLangParser.Create(customLogger));
    }

    class ParserExceptionSimulatingErrorReporter : ConsoleErrorReporter {
      private int numberOfErrors = 0;
      public string LastMessage = "";
      public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
        numberOfErrors++;
        if (level == ErrorLevel.Error) {
          if (numberOfErrors == 1) {
            throw new Exception("Simulated parser internal error");
          }

          LastMessage = ErrorToString(level, tok, msg);
          return true;
        }

        return false;
      }

      public override int Count(ErrorLevel level) {
        throw new NotImplementedException();
      }
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public void DocumentWithParserExceptionDisplaysIt() {
      var source = "function t() { / }";
      var documentItem = CreateTestDocument(source, TestFilePath);
      var errorReporter = new ParserExceptionSimulatingErrorReporter();
      parser.Parse(documentItem, errorReporter, CancellationToken);
      Assert.AreEqual($"encountered an exception while parsing file:///{TestFilePath}", customLogger.LastDebugMessage);
      Assert.AreEqual($"/{TestFilePath}(1,0): Error: [internal error] Parser exception: Simulated parser internal error", errorReporter.LastMessage);
    }
  }
}
