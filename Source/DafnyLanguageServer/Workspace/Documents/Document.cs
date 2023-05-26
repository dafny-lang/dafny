using System;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
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

    public virtual IEnumerable<DafnyDiagnostic> AllFileDiagnostics => Enumerable.Empty<DafnyDiagnostic>();

    public IdeState InitialIdeState(DafnyOptions options) {
      return ToIdeState(new IdeState(TextDocumentItem, Array.Empty<Diagnostic>(),
        SymbolTable.Empty(), SignatureAndCompletionTable.Empty(options, TextDocumentItem), new Dictionary<ImplementationId, IdeImplementationView>(),
        Array.Empty<Counterexample>(),
        false, Array.Empty<Diagnostic>(),
        GetInitialDocumentVerificationTree()));
    }

    public virtual VerificationTree GetInitialDocumentVerificationTree() {
      return new DocumentVerificationTree(TextDocumentItem);
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

  public record ImplementationView(Range Range, PublishedVerificationStatus Status, IReadOnlyList<DafnyDiagnostic> Diagnostics);

  public record BufferLine(int LineNumber, int StartIndex, int EndIndex);
}
