using System;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Diagnostics.Metrics;
using System.Linq;
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
  /// Asynchronous compilation tasks use this instance to synchronise on.
  ///
  /// When verification starts, no new instances of Compilation will be created for this version.
  /// There can be different verification threads that update the state of this object.
  /// </summary>
  public class Document {
    public DocumentTextBuffer TextDocumentItem { get; }
    public DocumentUri Uri => TextDocumentItem.Uri;
    public int Version => TextDocumentItem.Version!.Value;

    public Document(DocumentTextBuffer textDocumentItem) {
      TextDocumentItem = textDocumentItem;
    }

    public virtual IEnumerable<Diagnostic> Diagnostics => Enumerable.Empty<Diagnostic>();

    public IdeState InitialIdeState() {
      return ToIdeState(new IdeState(TextDocumentItem, Array.Empty<Diagnostic>(),
        SymbolTable.Empty(TextDocumentItem), new Dictionary<ImplementationId, ImplementationView>(),
        Array.Empty<Counterexample>(),
        false, Array.Empty<Diagnostic>(),
        new DocumentVerificationTree(TextDocumentItem)));
    }

    /// <summary>
    /// Collects information to present to the IDE
    /// </summary>
    public virtual IdeState ToIdeState(IdeState previousState) {
      return previousState with {
        TextDocumentItem = TextDocumentItem,
        ImplementationsWereUpdated = false,
      };
    }
  }

  public class DocumentAfterParsing : Document {
    private readonly IReadOnlyList<Diagnostic> parseDiagnostics;

    public DocumentAfterParsing(DocumentTextBuffer textDocumentItem,
      Dafny.Program program,
      IReadOnlyList<Diagnostic> parseDiagnostics) : base(textDocumentItem) {
      this.parseDiagnostics = parseDiagnostics;
      Program = program;
    }

    public override IEnumerable<Diagnostic> Diagnostics => parseDiagnostics;

    public Dafny.Program Program { get; }

    public override IdeState ToIdeState(IdeState previousState) {
      return previousState with {
        TextDocumentItem = TextDocumentItem,
        ResolutionDiagnostics = parseDiagnostics,
        ImplementationsWereUpdated = false,
      };
    }
  }

  public class DocumentAfterResolution : DocumentAfterParsing {
    public DocumentAfterResolution(DocumentTextBuffer textDocumentItem,
      Dafny.Program program,
      IReadOnlyList<Diagnostic> parseAndResolutionDiagnostics,
      SymbolTable symbolTable,
      IReadOnlyList<Diagnostic> ghostDiagnostics) :
      base(textDocumentItem, program, ArraySegment<Diagnostic>.Empty) {
      ParseAndResolutionDiagnostics = parseAndResolutionDiagnostics;
      SymbolTable = symbolTable;
      GhostDiagnostics = ghostDiagnostics;
    }

    public IReadOnlyList<Diagnostic> ParseAndResolutionDiagnostics { get; }
    public SymbolTable SymbolTable { get; }
    public IReadOnlyList<Diagnostic> GhostDiagnostics { get; }

    public override IEnumerable<Diagnostic> Diagnostics => ParseAndResolutionDiagnostics;

    public override IdeState ToIdeState(IdeState previousState) {
      return previousState with {
        TextDocumentItem = TextDocumentItem,
        ImplementationsWereUpdated = false,
        ResolutionDiagnostics = ParseAndResolutionDiagnostics,
        SymbolTable = SymbolTable.Resolved ? SymbolTable : previousState.SymbolTable,
        GhostDiagnostics = GhostDiagnostics
      };
    }
  }

  public class DocumentAfterTranslation : DocumentAfterResolution {
    public DocumentAfterTranslation(
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
        services.GetRequiredService<INotificationPublisher>());
    }

    public override IdeState ToIdeState(IdeState previousState) {
      var implementationViewsWithMigratedDiagnostics = ImplementationIdToView.Select(kv => {
        var value = kv.Value.Status < PublishedVerificationStatus.Error
          ? kv.Value with {
            Diagnostics = previousState.ImplementationIdToView.GetValueOrDefault(kv.Key)?.Diagnostics ?? kv.Value.Diagnostics
          }
          : kv.Value;
        return new KeyValuePair<ImplementationId, ImplementationView>(kv.Key, value);
      });
      return base.ToIdeState(previousState) with {
        ImplementationsWereUpdated = true,
        VerificationTree = VerificationTree,
        Counterexamples = new List<Counterexample>(Counterexamples),
        ImplementationIdToView = new Dictionary<ImplementationId, ImplementationView>(implementationViewsWithMigratedDiagnostics)
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
