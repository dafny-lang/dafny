using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Text document loader implementation that offloads the whole load procedure on one dedicated
  /// thread with a stack size of 256MB. Since only one thread is used, document loading is implicitely synchronized.
  /// The verification runs on the calling thread.
  /// </summary>
  /// <remarks>
  /// The increased stack size is necessary to solve the issue https://github.com/dafny-lang/dafny/issues/1447.
  /// </remarks>
  public class TextDocumentLoader : ITextDocumentLoader {

    private readonly IDafnyParser parser;
    private readonly ISymbolResolver symbolResolver;
    private readonly ISymbolTableFactory symbolTableFactory;
    private readonly IGhostStateDiagnosticCollector ghostStateDiagnosticCollector;
    protected readonly ICompilationStatusNotificationPublisher statusPublisher;
    protected readonly ILoggerFactory loggerFactory;

    protected TextDocumentLoader(
      ILoggerFactory loggerFactory,
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      ISymbolTableFactory symbolTableFactory,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher statusPublisher) {
      this.parser = parser;
      this.symbolResolver = symbolResolver;
      this.symbolTableFactory = symbolTableFactory;
      this.ghostStateDiagnosticCollector = ghostStateDiagnosticCollector;
      this.statusPublisher = statusPublisher;
      this.loggerFactory = loggerFactory;
    }

    public static TextDocumentLoader Create(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      ISymbolTableFactory symbolTableFactory,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher statusPublisher,
      ILoggerFactory loggerFactory
      ) {
      return new TextDocumentLoader(loggerFactory, parser, symbolResolver, symbolTableFactory, ghostStateDiagnosticCollector, statusPublisher);
    }

    public IdeState CreateUnloaded(VersionedTextDocumentIdentifier documentIdentifier, CancellationToken cancellationToken) {
      return CreateDocumentWithEmptySymbolTable(documentIdentifier, Array.Empty<Diagnostic>());
    }

    public async Task<CompilationAfterParsing> LoadAsync(DafnyOptions options, VersionedTextDocumentIdentifier documentIdentifier,
      CancellationToken cancellationToken) {
#pragma warning disable CS1998
      return await await DafnyMain.LargeStackFactory.StartNew(
        async () => LoadInternal(options, documentIdentifier, cancellationToken), cancellationToken
#pragma warning restore CS1998
        );
    }

    private CompilationAfterParsing LoadInternal(DafnyOptions options, VersionedTextDocumentIdentifier documentIdentifier,
      CancellationToken cancellationToken) {
      var errorReporter = new DiagnosticErrorReporter(options, documentIdentifier.Uri);
      statusPublisher.SendStatusNotification(documentIdentifier, CompilationStatus.Parsing);
      var program = parser.Parse(documentIdentifier, errorReporter, cancellationToken);
      var documentAfterParsing = new CompilationAfterParsing(documentIdentifier, program, errorReporter.AllDiagnosticsCopy);
      if (errorReporter.HasErrors) {
        statusPublisher.SendStatusNotification(documentIdentifier, CompilationStatus.ParsingFailed);
        return documentAfterParsing;
      }

      statusPublisher.SendStatusNotification(documentIdentifier, CompilationStatus.ResolutionStarted);
      try {
        var compilationUnit = symbolResolver.ResolveSymbols(documentIdentifier, program, cancellationToken);
        var legacySymbolTable = symbolTableFactory.CreateFrom(compilationUnit, cancellationToken);

        var newSymbolTable = errorReporter.HasErrors
          ? null
          : symbolTableFactory.CreateFrom(program, documentAfterParsing, cancellationToken);
        if (errorReporter.HasErrors) {
          statusPublisher.SendStatusNotification(documentIdentifier, CompilationStatus.ResolutionFailed);
        } else {
          statusPublisher.SendStatusNotification(documentIdentifier, CompilationStatus.CompilationSucceeded);
        }

        var ghostDiagnostics = ghostStateDiagnosticCollector.GetGhostStateDiagnostics(legacySymbolTable, cancellationToken)
          .ToArray();

        return new CompilationAfterResolution(documentIdentifier,
          program,
          errorReporter.AllDiagnosticsCopy,
          newSymbolTable,
          legacySymbolTable,
          ghostDiagnostics
        );
      } catch (OperationCanceledException) {
        return documentAfterParsing;
      }
    }

    private IdeState CreateDocumentWithEmptySymbolTable(
      VersionedTextDocumentIdentifier textDocument,
      IReadOnlyList<Diagnostic> diagnostics
    ) {
      var dafnyOptions = DafnyOptions.Default;
      return new IdeState(
        textDocument,
        new EmptyNode(),
        diagnostics,
        SymbolTable.Empty(),
        SignatureAndCompletionTable.Empty(dafnyOptions, textDocument),
        new Dictionary<ImplementationId, IdeImplementationView>(),
        Array.Empty<Counterexample>(),
        false,
        Array.Empty<Diagnostic>(),
null);
    }
  }
}


public record ImplementationId(Position NamedVerificationTask, string Name);
