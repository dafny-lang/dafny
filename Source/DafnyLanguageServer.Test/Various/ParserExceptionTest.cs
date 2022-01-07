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
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {


  [TestClass]
  public class ParserExceptionTest : DafnyLanguageServerTestBase {
    private const int MaxTestExecutionTimeMs = 10000;

    private DafnyLangParser parser;
    private IDictionary<string, string> configuration;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public class CustomLogger : ILogger<DafnyLangParser> {
      public string Text = "";
      public void Log<TState>(LogLevel logLevel, EventId eventId, TState state, Exception exception, Func<TState, Exception, string> formatter) {
        if (logLevel is LogLevel.Trace or LogLevel.Debug or LogLevel.Information or LogLevel.Warning) {
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

    public Task SetUp(IDictionary<string, string> configuration) {
      this.configuration = configuration;
      return Task.Run(() => parser = DafnyLangParser.Create(customLogger));
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task DocumentWithParserExceptionDisplaysIt() {
      var source = @"/".TrimStart();
      var documentItem = CreateTestDocument(source);
      // TODO: Put a custom error reporter that will throw an exception on the first error, but not the second one.
      parser.Parse(documentItem, null!, CancellationToken);

      Assert.AreEqual(customLogger.Text, "");
    }
  }
}
