﻿using System;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Diagnostics.Metrics;
using System.Linq;
using System.Net.Mime;
using System.Threading;
using IntervalTree;
using Microsoft.Boogie;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
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
        SymbolTable.Empty(), SignatureAndCompletionTable.Empty(TextDocumentItem), new Dictionary<ImplementationId, ImplementationView>(),
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

  public class DocumentAfterTranslation : DocumentAfterResolution {
    public DocumentAfterTranslation(
      IServiceProvider services,
      DocumentTextBuffer textDocumentItem,
      Dafny.Program program,
      IReadOnlyList<Diagnostic> parseAndResolutionDiagnostics,
      SymbolTable? newSymbolTable,
      SignatureAndCompletionTable signatureAndCompletionTable,
      IReadOnlyList<Diagnostic> ghostDiagnostics,
      IReadOnlyList<IImplementationTask> verificationTasks,
      List<Counterexample> counterexamples,
      Dictionary<ImplementationId, ImplementationView> implementationIdToView,
      VerificationTree verificationTree)
      : base(textDocumentItem, program, parseAndResolutionDiagnostics, newSymbolTable, signatureAndCompletionTable, ghostDiagnostics) {
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

  public class DocumentTextBuffer {
    public TextDocumentItem TextDocumentItem { get; }
    public TextBuffer Buffer { get; }
    public DocumentTextBuffer(TextDocumentItem documentItem) {
      TextDocumentItem = documentItem;
      Buffer = new TextBuffer(documentItem.Text);
    }
    
    public Position FromIndex(int index) {
      return Buffer.FromIndex(index);
    }
    
    public int ToIndex(Position position) {
      return Buffer.ToIndex(position);
    }

    public static implicit operator TextDocumentItem(DocumentTextBuffer buffer) => buffer.TextDocumentItem;
    public string Text => TextDocumentItem.Text;
    public DocumentUri Uri => TextDocumentItem.Uri;
    public int? Version => TextDocumentItem.Version;

    public int NumberOfLines => Buffer.Lines.Count;
  }

  public record BufferLine(int LineNumber, int StartIndex, int EndIndex);
  
  public class TextBuffer {
    public string Text { get; }

    private readonly IIntervalTree<int, BufferLine> indexToLineTree = new IntervalTree<int, BufferLine>();
    public readonly IReadOnlyList<BufferLine> Lines;

    private TextBuffer(string text, IReadOnlyList<BufferLine> lines) {
      Text = text;
      Lines = lines;
      
      foreach (var lineInfo in lines) {
        indexToLineTree.Add(lineInfo.StartIndex, lineInfo.EndIndex, lineInfo);
      }
    }
    
    public TextBuffer(string text) : this(text, ComputeLines(text, 0, text.Length)) { }

    private static List<BufferLine> ComputeLines(string text, int startIndex, int endIndex)
    {
      var lines = new List<BufferLine>();
      for (var index = 0; index < endIndex; index++)
      {
        if (text[index] == '\n')
        {
          lines.Add(new BufferLine(lines.Count, startIndex, index));
          startIndex = index + 1;
        }

        if (text.Substring(index, 2) == "\r\n")
        {
          lines.Add(new BufferLine(lines.Count, startIndex, index));
          startIndex = index + 2;
        }
      }

      lines.Add(new BufferLine(lines.Count, startIndex, endIndex));
      return lines;
    }

    public Position FromIndex(int index) {
      var line = IndexToLine(index);
      return new Position(line.LineNumber, index - line.StartIndex);
    }

    private BufferLine IndexToLine(int index)
    {
      return indexToLineTree.Query(index).Single();
    }

    public int ToIndex(Position position) {
      return Lines[position.Line].StartIndex + position.Character;
    }

    public TextBuffer ApplyTextChange(TextDocumentContentChangeEvent change) {
      if (change.Range == null) {
        // https://microsoft.github.io/language-server-protocol/specifications/specification-3-17/#textDocumentContentChangeEvent
        return new TextBuffer(change.Text);
      }

      int startIndex = ToIndex(change.Range.Start);
      int endIndex = ToIndex(change.Range.End);
      var newText = Text[..startIndex] + change.Text + Text[endIndex..];
      var changeStartLine = IndexToLine(startIndex);
      var changeEndLine = IndexToLine(endIndex);
      var freshLines = ComputeLines(newText, changeStartLine.StartIndex, changeEndLine.EndIndex + change.Text.Length);
      var newTotalLines = Lines.Take(changeStartLine.LineNumber).Concat(freshLines).Concat(Lines.TakeLast(changeEndLine.LineNumber));
      return new TextBuffer(newText, newTotalLines.ToList());
    }
  }
}
