using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit;

public class GhostStateDiagnosticCollectorTest {
  private GhostStateDiagnosticCollector ghostStateDiagnosticCollector;

  class DummyLogger : ILogger<GhostStateDiagnosticCollector> {
    public void Log<TState>(LogLevel logLevel, EventId eventId, TState state, Exception exception, Func<TState, Exception, string> formatter) {
      // Do nothing
    }

    public bool IsEnabled(LogLevel logLevel) {
      return true;
    }

    public IDisposable BeginScope<TState>(TState state) {
      return null;
    }
  }

  public GhostStateDiagnosticCollectorTest() {
    var options = new DafnyOptions();
    options.Set(ServerCommand.GhostIndicators, true);
    ghostStateDiagnosticCollector = new GhostStateDiagnosticCollector(
      options,
      new DummyLogger());
  }

  class CollectingErrorReporter : BatchErrorReporter {
    public Dictionary<ErrorLevel, List<DafnyDiagnostic>> GetErrors() {
      return this.AllMessages;
    }

    public CollectingErrorReporter(DafnyOptions options) : base(options) {
    }
  }

  class DummyModuleDecl : LiteralModuleDecl {
    public DummyModuleDecl() : base(
      new DefaultModuleDefinition(), null) {
    }
    public override object Dereference() {
      return this;
    }
  }

  [Fact]
  public void EnsureResilienceAgainstErrors() {
    // Builtins is null to trigger an error.
    var options = DafnyOptions.DefaultImmutableOptions;
    var reporter = new CollectingErrorReporter(options);
    var program = new Dafny.Program("dummy", new DummyModuleDecl(), null, reporter);
    var ghostDiagnostics = ghostStateDiagnosticCollector.GetGhostStateDiagnostics(
      new SignatureAndCompletionTable(null!, new CompilationUnit(new Uri(Directory.GetCurrentDirectory()), program),
        null!, null!, new IntervalTree<Position, ILocalizableSymbol>(), true)
      , CancellationToken.None);
    Assert.Empty(ghostDiagnostics);
  }
}
