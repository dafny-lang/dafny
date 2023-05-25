﻿using System;
using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Language;
using System.IO;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit {

  public class ParserExceptionTest {
    private static readonly string TestFilePath = "parserException.dfy";
    private const string LanguageId = "dafny";
    private const int MaxTestExecutionTimeMs = 10_000;
    private DafnyLangParser parser;
    private LastDebugLogger lastDebugLogger;

    public ParserExceptionTest(ITestOutputHelper output) {
      lastDebugLogger = new LastDebugLogger();
      parser = DafnyLangParser.Create(DafnyOptions.Create(new WriterFromOutputHelper(output)), lastDebugLogger);
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public void DocumentWithParserExceptionDisplaysIt() {
      var source = "function t() { / }";
      var options = new DafnyOptions(DafnyOptions.DefaultImmutableOptions);
      var documentItem = CreateTestDocument(source, TestFilePath);
      var uri = new Uri("file:///" + TestFilePath);
      var outerModule = new DefaultModuleDefinition(new List<Uri> { uri }, false);
      var errorReporter = new ParserExceptionSimulatingErrorReporter(options, outerModule);
      parser.Parse(new DocumentTextBuffer(documentItem), errorReporter, default);
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

      public ParserExceptionSimulatingErrorReporter(DafnyOptions options, DefaultModuleDefinition outerModule) : base(options, outerModule) {
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
