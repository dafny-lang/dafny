using System;
using System.Collections.Concurrent;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive.Concurrency;
using System.Reactive.Subjects;
using JetBrains.Annotations;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using SymbolTable = Microsoft.Dafny.LanguageServer.Language.Symbols.SymbolTable;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace {

  /// <summary>
  /// Internal representation of a specific version of a Dafny document.
  ///
  /// Only one instance should exist of a specific version.
  /// Asynchronous compilation tasks use this instance to synchronise on
  ///
  /// When verification starts, no new instances of DafnyDocument will be created for this version.
  /// There can be different verification threads that update the state of this object.
  /// </summary>
  /// <param name="TextDocumentItem">The text document represented by this dafny document.</param>
  /// <param name="Errors">The diagnostics to report.</param>
  /// <param name="GhostDiagnostics">The ghost state diagnostics of the document.</param>
  /// <param name="Program">The compiled Dafny program.</param>
  /// <param name="SymbolTable">The symbol table for the symbol lookups.</param>
  /// <param name="LoadCanceled"><c>true</c> if the document load was canceled for this document.</param>
  public class Compilation {
    public DocumentTextBuffer TextDocumentItem { get; }

    public DocumentUri Uri => TextDocumentItem.Uri;
    public int Version => TextDocumentItem.Version!.Value;

    public Compilation(DocumentTextBuffer textDocumentItem) {
      TextDocumentItem = textDocumentItem;
    }

    public virtual IEnumerable<Diagnostic> Diagnostics => Enumerable.Empty<Diagnostic>();

    /// <summary>
    /// Creates a clone of the DafnyDocument
    /// </summary>
    public virtual CompilationView Snapshot() {
      return new CompilationView(TextDocumentItem, Enumerable.Empty<Diagnostic>(),
        SymbolTable.Empty(TextDocumentItem), ImmutableDictionary<ImplementationId, ImplementationView>.Empty,
        false, false,
        ArraySegment<Diagnostic>.Empty,
        new DocumentVerificationTree(TextDocumentItem));
    }
  }

  public class ParsedCompilation : Compilation {
    private readonly IReadOnlyList<Diagnostic> parseDiagnostics;

    public ParsedCompilation(
      DocumentTextBuffer textDocumentItem,
      Dafny.Program program,
      IReadOnlyList<Diagnostic> parseDiagnostics) : base(textDocumentItem) {
      this.parseDiagnostics = parseDiagnostics;
      Program = program;
    }

    public override IEnumerable<Diagnostic> Diagnostics => parseDiagnostics;

    public Dafny.Program Program { get; }

    /// <summary>
    /// Checks if the given document uri is pointing to this dafny document.
    /// </summary>
    /// <param name="documentUri">The document uri to check.</param>
    /// <returns><c>true</c> if the specified document uri points to the file represented by this document.</returns>
    public bool IsDocument(DocumentUri documentUri) {
      return documentUri == Uri;
    }

    public override CompilationView Snapshot() {
      return new CompilationView(TextDocumentItem, parseDiagnostics,
        SymbolTable.Empty(TextDocumentItem), ImmutableDictionary<ImplementationId, ImplementationView>.Empty,
        false, false,
        ArraySegment<Diagnostic>.Empty,
        new DocumentVerificationTree(TextDocumentItem));
    }
  }

  public class ResolvedCompilation : ParsedCompilation {
    public ResolvedCompilation(
      DocumentTextBuffer textDocumentItem,
      Dafny.Program program,
      IReadOnlyList<Diagnostic> parseAndResolutionDiagnostics,
      SymbolTable symbolTable,
      IReadOnlyList<Diagnostic> ghostDiagnostics) : base(textDocumentItem, program, ArraySegment<Diagnostic>.Empty) {
      ParseAndResolutionDiagnostics = parseAndResolutionDiagnostics;
      SymbolTable = symbolTable;
      GhostDiagnostics = ghostDiagnostics;
    }

    public IReadOnlyList<Diagnostic> ParseAndResolutionDiagnostics { get; }
    public SymbolTable SymbolTable { get; }
    public IReadOnlyList<Diagnostic> GhostDiagnostics { get; }

    public override IEnumerable<Diagnostic> Diagnostics => ParseAndResolutionDiagnostics;

    public override CompilationView Snapshot() {
      return new CompilationView(TextDocumentItem, ParseAndResolutionDiagnostics,
        SymbolTable, ImmutableDictionary<ImplementationId, ImplementationView>.Empty,
        false, false,
        GhostDiagnostics,
        new DocumentVerificationTree(TextDocumentItem));
    }
  }

  public class TranslatedCompilation : ResolvedCompilation {
    public TranslatedCompilation(
      IServiceProvider services,
      DocumentTextBuffer textDocumentItem,
      Dafny.Program program,
      IReadOnlyList<Diagnostic> parseAndResolutionDiagnostics,
      SymbolTable symbolTable,
      IReadOnlyList<Diagnostic> ghostDiagnostics,
      IReadOnlyList<IImplementationTask> verificationTasks,
      List<Counterexample> counterexamples,
      Dictionary<ImplementationId, ImplementationView> implementationIdToView,
      VerificationTree verificationTree)
      : base(textDocumentItem, program, parseAndResolutionDiagnostics, symbolTable, ghostDiagnostics) {
      VerificationTree = verificationTree;
      VerificationTasks = verificationTasks;
      Counterexamples = counterexamples;
      ImplementationIdToView = implementationIdToView;

      GutterProgressReporter = new VerificationProgressReporter(
        services.GetRequiredService<ILogger<VerificationProgressReporter>>(),
        this,
        services.GetRequiredService<ICompilationStatusNotificationPublisher>(),
        services.GetRequiredService<INotificationPublisher>());
    }

    public override CompilationView Snapshot() {
      return base.Snapshot() with {
        ImplementationsWereUpdated = true,
        VerificationTree = VerificationTree,
        ImplementationViews = new Dictionary<ImplementationId, ImplementationView>(ImplementationIdToView)
      };
    }

    public override IEnumerable<Diagnostic> Diagnostics => base.Diagnostics.Concat(
      ImplementationIdToView.SelectMany(kv => kv.Value.Diagnostics) ?? Enumerable.Empty<Diagnostic>());

    /// <summary>
    /// Contains the real-time status of all verification efforts.
    /// Can be migrated from a previous document
    /// The position and the range are never sent to the client.
    /// </summary>
    public VerificationTree VerificationTree { get; set; }
    public IReadOnlyList<IImplementationTask> VerificationTasks { get; set; }
    public IVerificationProgressReporter GutterProgressReporter { get; set; }
    public List<Counterexample> Counterexamples { get; set; }
    public Dictionary<ImplementationId, ImplementationView> ImplementationIdToView { get; set; }
  }

  public record ImplementationView(Range Range, PublishedVerificationStatus Status, IReadOnlyList<Diagnostic> Diagnostics);

  public record DocumentTextBuffer(int NumberOfLines) : TextDocumentItem {
    public static DocumentTextBuffer From(TextDocumentItem textDocumentItem) {
      return new DocumentTextBuffer(TextChangeProcessor.ComputeNumberOfLines(textDocumentItem.Text)) {
        Text = textDocumentItem.Text,
        Uri = textDocumentItem.Uri,
        Version = textDocumentItem.Version,
        LanguageId = textDocumentItem.LanguageId
      };
    }
  }
}
