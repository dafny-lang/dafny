using System;
using System.Collections.Concurrent;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive.Concurrency;
using System.Reactive.Subjects;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using SymbolTable = Microsoft.Dafny.LanguageServer.Language.Symbols.SymbolTable;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
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
  public record DafnyDocument(
    DocumentTextBuffer TextDocumentItem,
    IReadOnlyList<Diagnostic> ParseAndResolutionDiagnostics,
    SymbolTable SymbolTable,
    bool CanDoVerification,
    IReadOnlyList<Diagnostic> GhostDiagnostics,
    Dafny.Program Program,
    bool WasResolved,
    bool LoadCanceled = false
  ) {

    public IReadOnlyList<IImplementationTask>? VerificationTasks { get; set; } = null;

    public IEnumerable<Diagnostic> Diagnostics => ParseAndResolutionDiagnostics.Concat(
      ImplementationIdToView?.SelectMany(kv => kv.Value.Diagnostics) ?? Enumerable.Empty<Diagnostic>());

    public DocumentUri Uri => TextDocumentItem.Uri;
    public int Version => TextDocumentItem.Version!.Value;


    /// <summary>
    /// Contains the real-time status of all verification efforts.
    /// Can be migrated from a previous document
    /// The position and the range are never sent to the client.
    /// </summary>
    public VerificationTree VerificationTree { get; set; } = new DocumentVerificationTree(
      TextDocumentItem.Uri.ToString(),
      TextDocumentItem.NumberOfLines
    );

    // List of a few last touched method positions
    public ImmutableList<Position> LastTouchedVerifiables { get; set; } = new List<Position>() { }.ToImmutableList();

    // Used to prioritize verification to one method and its dependencies
    public Range? LastChange { get; init; } = null;

    /// <summary>
    /// Checks if the given document uri is pointing to this dafny document.
    /// </summary>
    /// <param name="documentUri">The document uri to check.</param>
    /// <returns><c>true</c> if the specified document uri points to the file represented by this document.</returns>
    public bool IsDocument(DocumentUri documentUri) {
      return documentUri == Uri;
    }

    public int LinesCount => VerificationTree.Range.End.Line;
    public IVerificationProgressReporter? GutterProgressReporter { get; set; }
    public List<Counterexample>? Counterexamples { get; set; }
    public Dictionary<ImplementationId, ImplementationView>? ImplementationIdToView { get; set; }

    /// <summary>
    /// Creates a clone of the DafnyDocument
    /// </summary>
    public DafnyDocument Snapshot() {
      var result = new DafnyDocument(TextDocumentItem, ParseAndResolutionDiagnostics, SymbolTable, CanDoVerification, GhostDiagnostics,
        Program, WasResolved, LoadCanceled) {
        VerificationTree = VerificationTree,
        Counterexamples = Counterexamples == null ? null : new(Counterexamples),
        ImplementationIdToView = ImplementationIdToView == null ? null : new(ImplementationIdToView),
        LastTouchedVerifiables = LastTouchedVerifiables,
      };
      return result;
    }
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
