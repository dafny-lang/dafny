using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Threading;
using DafnyCore.Test;
using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

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

  public GhostStateDiagnosticCollectorTest(ITestOutputHelper output) {
    var options = new DafnyOptions(TextReader.Null, (TextWriter)new WriterFromOutputHelper(output), (TextWriter)new WriterFromOutputHelper(output));
    options.Set(GhostStateDiagnosticCollector.GhostIndicators, true);
    ghostStateDiagnosticCollector = new GhostStateDiagnosticCollector(
      options,
      new DummyLogger());
  }

  class CollectingErrorReporter : BatchErrorReporter {
    public Dictionary<ErrorLevel, List<DafnyDiagnostic>> GetErrors() {
      return this.AllMessagesByLevel;
    }

    public CollectingErrorReporter(DafnyOptions options) : base(options) {
    }
  }

  class DummyModuleDecl : LiteralModuleDecl {
    public DummyModuleDecl(DafnyOptions options) : base(options,
      new DefaultModuleDefinition(), null, Guid.NewGuid()) {
    }
    public override object Dereference() {
      return this;
    }
  }

  [Fact]
  public void EnsureResilienceAgainstErrors() {
    // Builtins is null to trigger an error.
    var options = DafnyOptions.DefaultImmutableOptions;
    var rootUri = new Uri(Directory.GetCurrentDirectory());
    var dummyModuleDecl = new DummyModuleDecl(options);
    var reporter = new CollectingErrorReporter(options);
    var compilation = new CompilationData(reporter, [], new List<Uri>(), Sets.Empty<Uri>(),
      Sets.Empty<Uri>());
    var program = new Dafny.Program("dummy", dummyModuleDecl, null, reporter, compilation);
    var source = new CancellationTokenSource();
    source.CancelAfter(TimeSpan.FromSeconds(50));
    var ghostDiagnostics = ghostStateDiagnosticCollector.GetGhostStateDiagnostics(
      new LegacySignatureAndCompletionTable(null!, new CompilationUnit(rootUri, program),
        null!, null!, ImmutableDictionary<Uri, IIntervalTree<Position, ILocalizableSymbol>>.Empty, true)
      , source.Token);
    Assert.Empty(ghostDiagnostics);
  }
}
